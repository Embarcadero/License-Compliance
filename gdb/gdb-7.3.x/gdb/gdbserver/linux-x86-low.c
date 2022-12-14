/* GNU/Linux/x86-64 specific low level interface, for the remote server
   for GDB.
   Copyright (C) 2002, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011
   Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include <stddef.h>
#include <signal.h>
#include <limits.h>
#include "server.h"
#include "linux-low.h"
#include "i387-fp.h"
#include "i386-low.h"
#include "i386-xstate.h"
#include "elf/common.h"

#include "gdb_proc_service.h"

/* Defined in auto-generated file i386-linux.c.  */
void init_registers_i386_linux (void);
/* Defined in auto-generated file amd64-linux.c.  */
void init_registers_amd64_linux (void);
/* Defined in auto-generated file i386-avx-linux.c.  */
void init_registers_i386_avx_linux (void);
/* Defined in auto-generated file amd64-avx-linux.c.  */
void init_registers_amd64_avx_linux (void);
/* Defined in auto-generated file i386-mmx-linux.c.  */
void init_registers_i386_mmx_linux (void);

static unsigned char jump_insn[] = { 0xe9, 0, 0, 0, 0 };

/* Backward compatibility for gdb without XML support.  */

static const char *xmltarget_i386_linux_no_xml = "@<target>\
<architecture>i386</architecture>\
<osabi>GNU/Linux</osabi>\
</target>";

#ifdef __x86_64__
static const char *xmltarget_amd64_linux_no_xml = "@<target>\
<architecture>i386:x86-64</architecture>\
<osabi>GNU/Linux</osabi>\
</target>";
#endif

#ifdef HAVE_SYS_REG_H
#include <sys/reg.h>
#endif
#ifdef HAVE_SYS_PROCFS_H
#include <sys/procfs.h>
#endif

#include <sys/ptrace.h>
#include <sys/uio.h>

#ifndef PTRACE_GETREGSET
#define PTRACE_GETREGSET	0x4204
#endif

#ifndef PTRACE_SETREGSET
#define PTRACE_SETREGSET	0x4205
#endif


#ifndef PTRACE_GET_THREAD_AREA
#define PTRACE_GET_THREAD_AREA 25
#endif

/* This definition comes from prctl.h, but some kernels may not have it.  */
#ifndef PTRACE_ARCH_PRCTL
#define PTRACE_ARCH_PRCTL      30
#endif

#define PTRACE_ARG3_TYPE       void*
#define PTRACE_ARG4_TYPE       void*

/* The following definitions come from prctl.h, but may be absent
   for certain configurations.  */
#ifndef ARCH_GET_FS
#define ARCH_SET_GS 0x1001
#define ARCH_SET_FS 0x1002
#define ARCH_GET_FS 0x1003
#define ARCH_GET_GS 0x1004
#endif

/* Per-process arch-specific data we want to keep.  */

struct arch_process_info
{
  struct i386_debug_reg_state debug_reg_state;
};

/* Per-thread arch-specific data we want to keep.  */

struct arch_lwp_info
{
  /* Non-zero if our copy differs from what's recorded in the thread.  */
  int debug_registers_changed;
};

#ifdef __x86_64__

/* Mapping between the general-purpose registers in `struct user'
   format and GDB's register array layout.
   Note that the transfer layout uses 64-bit regs.  */
static /*const*/ int i386_regmap[] = 
{
  RAX * 8, RCX * 8, RDX * 8, RBX * 8,
  RSP * 8, RBP * 8, RSI * 8, RDI * 8,
  RIP * 8, EFLAGS * 8, CS * 8, SS * 8,
  DS * 8, ES * 8, FS * 8, GS * 8
};

#define I386_NUM_REGS (sizeof (i386_regmap) / sizeof (i386_regmap[0]))

/* So code below doesn't have to care, i386 or amd64.  */
#define ORIG_EAX ORIG_RAX

static const int x86_64_regmap[] =
{
  RAX * 8, RBX * 8, RCX * 8, RDX * 8,
  RSI * 8, RDI * 8, RBP * 8, RSP * 8,
  R8 * 8, R9 * 8, R10 * 8, R11 * 8,
  R12 * 8, R13 * 8, R14 * 8, R15 * 8,
  RIP * 8, EFLAGS * 8, CS * 8, SS * 8,
  DS * 8, ES * 8, FS * 8, GS * 8,
  -1, -1, -1, -1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, -1, -1, -1, -1,
  ORIG_RAX * 8
};

#define X86_64_NUM_REGS (sizeof (x86_64_regmap) / sizeof (x86_64_regmap[0]))

#else /* ! __x86_64__ */

/* Mapping between the general-purpose registers in `struct user'
   format and GDB's register array layout.  */
static /*const*/ int i386_regmap[] = 
{
  EAX * 4, ECX * 4, EDX * 4, EBX * 4,
  UESP * 4, EBP * 4, ESI * 4, EDI * 4,
  EIP * 4, EFL * 4, CS * 4, SS * 4,
  DS * 4, ES * 4, FS * 4, GS * 4
};

#define I386_NUM_REGS (sizeof (i386_regmap) / sizeof (i386_regmap[0]))

#endif

/* Called by libthread_db.  */

ps_err_e
ps_get_thread_area (const struct ps_prochandle *ph,
		    lwpid_t lwpid, int idx, void **base)
{
#ifdef __x86_64__
  int use_64bit = register_size (0) == 8;

  if (use_64bit)
    {
      switch (idx)
	{
	case FS:
	  if (ptrace (PTRACE_ARCH_PRCTL, lwpid, base, ARCH_GET_FS) == 0)
	    return PS_OK;
	  break;
	case GS:
	  if (ptrace (PTRACE_ARCH_PRCTL, lwpid, base, ARCH_GET_GS) == 0)
	    return PS_OK;
	  break;
	default:
	  return PS_BADADDR;
	}
      return PS_ERR;
    }
#endif

  {
    unsigned int desc[4];

    if (ptrace (PTRACE_GET_THREAD_AREA, lwpid,
		(void *) (intptr_t) idx, (PTRACE_ARG4_TYPE) &desc) < 0)
      return PS_ERR;

    *(int *)base = desc[1];
    return PS_OK;
  }
}

/* Get the thread area address.  This is used to recognize which
   thread is which when tracing with the in-process agent library.  We
   don't read anything from the address, and treat it as opaque; it's
   the address itself that we assume is unique per-thread.  */

static int
x86_get_thread_area (int lwpid, CORE_ADDR *addr)
{
#ifdef __x86_64__
  int use_64bit = register_size (0) == 8;

  if (use_64bit)
    {
      void *base;
      if (ptrace (PTRACE_ARCH_PRCTL, lwpid, &base, ARCH_GET_FS) == 0)
	{
	  *addr = (CORE_ADDR) (uintptr_t) base;
	  return 0;
	}

      return -1;
    }
#endif

  {
    struct lwp_info *lwp = find_lwp_pid (pid_to_ptid (lwpid));
    struct regcache *regcache = get_thread_regcache (get_lwp_thread (lwp), 1);
    unsigned int desc[4];
    ULONGEST gs = 0;
    const int reg_thread_area = 3; /* bits to scale down register value.  */
    int idx;

    collect_register_by_name (regcache, "gs", &gs);

    idx = gs >> reg_thread_area;

    if (ptrace (PTRACE_GET_THREAD_AREA,
		lwpid_of (lwp),
		(void *) (long) idx, (PTRACE_ARG4_TYPE) &desc) < 0)
      return -1;

    *addr = desc[1];
    return 0;
  }
}



static int
i386_cannot_store_register (int regno)
{
  return regno >= I386_NUM_REGS;
}

static int
i386_cannot_fetch_register (int regno)
{
  return regno >= I386_NUM_REGS;
}

static void
x86_fill_gregset (struct regcache *regcache, void *buf)
{
  int i;

#ifdef __x86_64__
  if (register_size (0) == 8)
    {
      for (i = 0; i < X86_64_NUM_REGS; i++)
	if (x86_64_regmap[i] != -1)
	  collect_register (regcache, i, ((char *) buf) + x86_64_regmap[i]);
      return;
    }
#endif

  for (i = 0; i < I386_NUM_REGS; i++)
    collect_register (regcache, i, ((char *) buf) + i386_regmap[i]);

  collect_register_by_name (regcache, "orig_eax",
			    ((char *) buf) + ORIG_EAX * 4);
}

static void
x86_store_gregset (struct regcache *regcache, const void *buf)
{
  int i;

#ifdef __x86_64__
  if (register_size (0) == 8)
    {
      for (i = 0; i < X86_64_NUM_REGS; i++)
	if (x86_64_regmap[i] != -1)
	  supply_register (regcache, i, ((char *) buf) + x86_64_regmap[i]);
      return;
    }
#endif

  for (i = 0; i < I386_NUM_REGS; i++)
    supply_register (regcache, i, ((char *) buf) + i386_regmap[i]);

  supply_register_by_name (regcache, "orig_eax",
			   ((char *) buf) + ORIG_EAX * 4);
}

static void
x86_fill_fpregset (struct regcache *regcache, void *buf)
{
#ifdef __x86_64__
  i387_cache_to_fxsave (regcache, buf);
#else
  i387_cache_to_fsave (regcache, buf);
#endif
}

static void
x86_store_fpregset (struct regcache *regcache, const void *buf)
{
#ifdef __x86_64__
  i387_fxsave_to_cache (regcache, buf);
#else
  i387_fsave_to_cache (regcache, buf);
#endif
}

#ifndef __x86_64__

static void
x86_fill_fpxregset (struct regcache *regcache, void *buf)
{
  i387_cache_to_fxsave (regcache, buf);
}

static void
x86_store_fpxregset (struct regcache *regcache, const void *buf)
{
  i387_fxsave_to_cache (regcache, buf);
}

#endif

static void
x86_fill_xstateregset (struct regcache *regcache, void *buf)
{
  i387_cache_to_xsave (regcache, buf);
}

static void
x86_store_xstateregset (struct regcache *regcache, const void *buf)
{
  i387_xsave_to_cache (regcache, buf);
}

/* ??? The non-biarch i386 case stores all the i387 regs twice.
   Once in i387_.*fsave.* and once in i387_.*fxsave.*.
   This is, presumably, to handle the case where PTRACE_[GS]ETFPXREGS
   doesn't work.  IWBN to avoid the duplication in the case where it
   does work.  Maybe the arch_setup routine could check whether it works
   and update target_regsets accordingly, maybe by moving target_regsets
   to linux_target_ops and set the right one there, rather than having to
   modify the target_regsets global.  */

struct regset_info target_regsets[] =
{
#ifdef HAVE_PTRACE_GETREGS
  { PTRACE_GETREGS, PTRACE_SETREGS, 0, sizeof (elf_gregset_t),
    GENERAL_REGS,
    x86_fill_gregset, x86_store_gregset },
  { PTRACE_GETREGSET, PTRACE_SETREGSET, NT_X86_XSTATE, 0,
    EXTENDED_REGS, x86_fill_xstateregset, x86_store_xstateregset },
# ifndef __x86_64__
#  ifdef HAVE_PTRACE_GETFPXREGS
  { PTRACE_GETFPXREGS, PTRACE_SETFPXREGS, 0, sizeof (elf_fpxregset_t),
    EXTENDED_REGS,
    x86_fill_fpxregset, x86_store_fpxregset },
#  endif
# endif
  { PTRACE_GETFPREGS, PTRACE_SETFPREGS, 0, sizeof (elf_fpregset_t),
    FP_REGS,
    x86_fill_fpregset, x86_store_fpregset },
#endif /* HAVE_PTRACE_GETREGS */
  { 0, 0, 0, -1, -1, NULL, NULL }
};

static CORE_ADDR
x86_get_pc (struct regcache *regcache)
{
  int use_64bit = register_size (0) == 8;

  if (use_64bit)
    {
      unsigned long pc;
      collect_register_by_name (regcache, "rip", &pc);
      return (CORE_ADDR) pc;
    }
  else
    {
      unsigned int pc;
      collect_register_by_name (regcache, "eip", &pc);
      return (CORE_ADDR) pc;
    }
}

static void
x86_set_pc (struct regcache *regcache, CORE_ADDR pc)
{
  int use_64bit = register_size (0) == 8;

  if (use_64bit)
    {
      unsigned long newpc = pc;
      supply_register_by_name (regcache, "rip", &newpc);
    }
  else
    {
      unsigned int newpc = pc;
      supply_register_by_name (regcache, "eip", &newpc);
    }
}

static const unsigned char x86_breakpoint[] = { 0xCC };
#define x86_breakpoint_len 1

static int
x86_breakpoint_at (CORE_ADDR pc)
{
  unsigned char c;

  (*the_target->read_memory) (pc, &c, 1);
  if (c == 0xCC)
    return 1;

  return 0;
}

/* Support for debug registers.  */

static unsigned long
x86_linux_dr_get (ptid_t ptid, int regnum)
{
  int tid;
  unsigned long value;

  tid = ptid_get_lwp (ptid);

  errno = 0;
  value = ptrace (PTRACE_PEEKUSER, tid,
		  (PTRACE_ARG3_TYPE)offsetof (struct user, u_debugreg[regnum]), 0);
  if (errno != 0)
    error ("Couldn't read debug register");

  return value;
}

static void
x86_linux_dr_set (ptid_t ptid, int regnum, unsigned long value)
{
  int tid;

  tid = ptid_get_lwp (ptid);

  errno = 0;
  ptrace (PTRACE_POKEUSER, tid,
	  (PTRACE_ARG3_TYPE)offsetof (struct user, u_debugreg[regnum]), (PTRACE_ARG4_TYPE)value);
  if (errno != 0)
    error ("Couldn't write debug register");
}

static int
update_debug_registers_callback (struct inferior_list_entry *entry,
				 void *pid_p)
{
  struct lwp_info *lwp = (struct lwp_info *) entry;
  int pid = *(int *) pid_p;

  /* Only update the threads of this process.  */
  if (pid_of (lwp) == pid)
    {
      /* The actual update is done later just before resuming the lwp,
	 we just mark that the registers need updating.  */
      lwp->arch_private->debug_registers_changed = 1;

      /* If the lwp isn't stopped, force it to momentarily pause, so
	 we can update its debug registers.  */
      if (!lwp->stopped)
	linux_stop_lwp (lwp);
    }

  return 0;
}

/* Update the inferior's debug register REGNUM from STATE.  */

void
i386_dr_low_set_addr (const struct i386_debug_reg_state *state, int regnum)
{
  /* Only update the threads of this process.  */
  int pid = pid_of (get_thread_lwp (current_inferior));

  if (! (regnum >= 0 && regnum <= DR_LASTADDR - DR_FIRSTADDR))
    fatal ("Invalid debug register %d", regnum);

  find_inferior (&all_lwps, update_debug_registers_callback, &pid);
}

/* Return the inferior's debug register REGNUM.  */

CORE_ADDR
i386_dr_low_get_addr (int regnum)
{
  struct lwp_info *lwp = get_thread_lwp (current_inferior);
  ptid_t ptid = ptid_of (lwp);

  /* DR6 and DR7 are retrieved with some other way.  */
  gdb_assert (DR_FIRSTADDR <= regnum && regnum <= DR_LASTADDR);

  return x86_linux_dr_get (ptid, regnum);
}

/* Update the inferior's DR7 debug control register from STATE.  */

void
i386_dr_low_set_control (const struct i386_debug_reg_state *state)
{
  /* Only update the threads of this process.  */
  int pid = pid_of (get_thread_lwp (current_inferior));

  find_inferior (&all_lwps, update_debug_registers_callback, &pid);
}

/* Return the inferior's DR7 debug control register.  */

unsigned
i386_dr_low_get_control (void)
{
  struct lwp_info *lwp = get_thread_lwp (current_inferior);
  ptid_t ptid = ptid_of (lwp);

  return x86_linux_dr_get (ptid, DR_CONTROL);
}

/* Get the value of the DR6 debug status register from the inferior
   and record it in STATE.  */

unsigned
i386_dr_low_get_status (void)
{
  struct lwp_info *lwp = get_thread_lwp (current_inferior);
  ptid_t ptid = ptid_of (lwp);

  return x86_linux_dr_get (ptid, DR_STATUS);
}

/* Breakpoint/Watchpoint support.  */

static int
x86_insert_point (char type, CORE_ADDR addr, int len)
{
  struct process_info *proc = current_process ();
  switch (type)
    {
    case '0':
      {
	int ret;

	ret = prepare_to_access_memory ();
	if (ret)
	  return -1;
	ret = set_gdb_breakpoint_at (addr);
	done_accessing_memory ();
	return ret;
      }
    case '2':
    case '3':
    case '4':
      return i386_low_insert_watchpoint (&proc->private->arch_private->debug_reg_state,
					 type, addr, len);
    default:
      /* Unsupported.  */
      return 1;
    }
}

static int
x86_remove_point (char type, CORE_ADDR addr, int len)
{
  struct process_info *proc = current_process ();
  switch (type)
    {
    case '0':
      {
	int ret;

	ret = prepare_to_access_memory ();
	if (ret)
	  return -1;
	ret = delete_gdb_breakpoint_at (addr);
	done_accessing_memory ();
	return ret;
      }
    case '2':
    case '3':
    case '4':
      return i386_low_remove_watchpoint (&proc->private->arch_private->debug_reg_state,
					 type, addr, len);
    default:
      /* Unsupported.  */
      return 1;
    }
}

static int
x86_stopped_by_watchpoint (void)
{
  struct process_info *proc = current_process ();
  return i386_low_stopped_by_watchpoint (&proc->private->arch_private->debug_reg_state);
}

static CORE_ADDR
x86_stopped_data_address (void)
{
  struct process_info *proc = current_process ();
  CORE_ADDR addr;
  if (i386_low_stopped_data_address (&proc->private->arch_private->debug_reg_state,
				     &addr))
    return addr;
  return 0;
}

/* Called when a new process is created.  */

static struct arch_process_info *
x86_linux_new_process (void)
{
  struct arch_process_info *info = xcalloc (1, sizeof (*info));

  i386_low_init_dregs (&info->debug_reg_state);

  return info;
}

/* Called when a new thread is detected.  */

static struct arch_lwp_info *
x86_linux_new_thread (void)
{
  struct arch_lwp_info *info = xcalloc (1, sizeof (*info));

  info->debug_registers_changed = 1;

  return info;
}

/* Called when resuming a thread.
   If the debug regs have changed, update the thread's copies.  */

static void
x86_linux_prepare_to_resume (struct lwp_info *lwp)
{
  ptid_t ptid = ptid_of (lwp);

  if (lwp->arch_private->debug_registers_changed)
    {
      int i;
      int pid = ptid_get_pid (ptid);
      struct process_info *proc = find_process_pid (pid);
      struct i386_debug_reg_state *state
	= &proc->private->arch_private->debug_reg_state;

      for (i = DR_FIRSTADDR; i <= DR_LASTADDR; i++)
	x86_linux_dr_set (ptid, i, state->dr_mirror[i]);

      x86_linux_dr_set (ptid, DR_CONTROL, state->dr_control_mirror);

      lwp->arch_private->debug_registers_changed = 0;
    }

  if (lwp->stopped_by_watchpoint)
    x86_linux_dr_set (ptid, DR_STATUS, 0);
}

/* When GDBSERVER is built as a 64-bit application on linux, the
   PTRACE_GETSIGINFO data is always presented in 64-bit layout.  Since
   debugging a 32-bit inferior with a 64-bit GDBSERVER should look the same
   as debugging it with a 32-bit GDBSERVER, we do the 32-bit <-> 64-bit
   conversion in-place ourselves.  */

/* These types below (compat_*) define a siginfo type that is layout
   compatible with the siginfo type exported by the 32-bit userspace
   support.  */

#ifdef __x86_64__

typedef int compat_int_t;
typedef unsigned int compat_uptr_t;

typedef int compat_time_t;
typedef int compat_timer_t;
typedef int compat_clock_t;

struct compat_timeval
{
  compat_time_t tv_sec;
  int tv_usec;
};

typedef union compat_sigval
{
  compat_int_t sival_int;
  compat_uptr_t sival_ptr;
} compat_sigval_t;

typedef struct compat_siginfo
{
  int si_signo;
  int si_errno;
  int si_code;

  union
  {
    int _pad[((128 / sizeof (int)) - 3)];

    /* kill() */
    struct
    {
      unsigned int _pid;
      unsigned int _uid;
    } _kill;

    /* POSIX.1b timers */
    struct
    {
      compat_timer_t _tid;
      int _overrun;
      compat_sigval_t _sigval;
    } _timer;

    /* POSIX.1b signals */
    struct
    {
      unsigned int _pid;
      unsigned int _uid;
      compat_sigval_t _sigval;
    } _rt;

    /* SIGCHLD */
    struct
    {
      unsigned int _pid;
      unsigned int _uid;
      int _status;
      compat_clock_t _utime;
      compat_clock_t _stime;
    } _sigchld;

    /* SIGILL, SIGFPE, SIGSEGV, SIGBUS */
    struct
    {
      unsigned int _addr;
    } _sigfault;

    /* SIGPOLL */
    struct
    {
      int _band;
      int _fd;
    } _sigpoll;
  } _sifields;
} compat_siginfo_t;

#define cpt_si_pid _sifields._kill._pid
#define cpt_si_uid _sifields._kill._uid
#define cpt_si_timerid _sifields._timer._tid
#define cpt_si_overrun _sifields._timer._overrun
#define cpt_si_status _sifields._sigchld._status
#define cpt_si_utime _sifields._sigchld._utime
#define cpt_si_stime _sifields._sigchld._stime
#define cpt_si_ptr _sifields._rt._sigval.sival_ptr
#define cpt_si_addr _sifields._sigfault._addr
#define cpt_si_band _sifields._sigpoll._band
#define cpt_si_fd _sifields._sigpoll._fd

/* glibc at least up to 2.3.2 doesn't have si_timerid, si_overrun.
   In their place is si_timer1,si_timer2.  */
#ifndef si_timerid
#define si_timerid si_timer1
#endif
#ifndef si_overrun
#define si_overrun si_timer2
#endif

static void
compat_siginfo_from_siginfo (compat_siginfo_t *to, siginfo_t *from)
{
  memset (to, 0, sizeof (*to));

  to->si_signo = from->si_signo;
  to->si_errno = from->si_errno;
  to->si_code = from->si_code;

  if (to->si_code == SI_TIMER)
    {
      to->cpt_si_timerid = from->si_timerid;
      to->cpt_si_overrun = from->si_overrun;
      to->cpt_si_ptr = (intptr_t) from->si_ptr;
    }
  else if (to->si_code == SI_USER)
    {
      to->cpt_si_pid = from->si_pid;
      to->cpt_si_uid = from->si_uid;
    }
  else if (to->si_code < 0)
    {
      to->cpt_si_pid = from->si_pid;
      to->cpt_si_uid = from->si_uid;
      to->cpt_si_ptr = (intptr_t) from->si_ptr;
    }
  else
    {
      switch (to->si_signo)
	{
	case SIGCHLD:
	  to->cpt_si_pid = from->si_pid;
	  to->cpt_si_uid = from->si_uid;
	  to->cpt_si_status = from->si_status;
	  to->cpt_si_utime = from->si_utime;
	  to->cpt_si_stime = from->si_stime;
	  break;
	case SIGILL:
	case SIGFPE:
	case SIGSEGV:
	case SIGBUS:
	  to->cpt_si_addr = (intptr_t) from->si_addr;
	  break;
	case SIGPOLL:
	  to->cpt_si_band = from->si_band;
	  to->cpt_si_fd = from->si_fd;
	  break;
	default:
	  to->cpt_si_pid = from->si_pid;
	  to->cpt_si_uid = from->si_uid;
	  to->cpt_si_ptr = (intptr_t) from->si_ptr;
	  break;
	}
    }
}

static void
siginfo_from_compat_siginfo (siginfo_t *to, compat_siginfo_t *from)
{
  memset (to, 0, sizeof (*to));

  to->si_signo = from->si_signo;
  to->si_errno = from->si_errno;
  to->si_code = from->si_code;

  if (to->si_code == SI_TIMER)
    {
      to->si_timerid = from->cpt_si_timerid;
      to->si_overrun = from->cpt_si_overrun;
      to->si_ptr = (void *) (intptr_t) from->cpt_si_ptr;
    }
  else if (to->si_code == SI_USER)
    {
      to->si_pid = from->cpt_si_pid;
      to->si_uid = from->cpt_si_uid;
    }
  else if (to->si_code < 0)
    {
      to->si_pid = from->cpt_si_pid;
      to->si_uid = from->cpt_si_uid;
      to->si_ptr = (void *) (intptr_t) from->cpt_si_ptr;
    }
  else
    {
      switch (to->si_signo)
	{
	case SIGCHLD:
	  to->si_pid = from->cpt_si_pid;
	  to->si_uid = from->cpt_si_uid;
	  to->si_status = from->cpt_si_status;
	  to->si_utime = from->cpt_si_utime;
	  to->si_stime = from->cpt_si_stime;
	  break;
	case SIGILL:
	case SIGFPE:
	case SIGSEGV:
	case SIGBUS:
	  to->si_addr = (void *) (intptr_t) from->cpt_si_addr;
	  break;
	case SIGPOLL:
	  to->si_band = from->cpt_si_band;
	  to->si_fd = from->cpt_si_fd;
	  break;
	default:
	  to->si_pid = from->cpt_si_pid;
	  to->si_uid = from->cpt_si_uid;
	  to->si_ptr = (void* ) (intptr_t) from->cpt_si_ptr;
	  break;
	}
    }
}

#endif /* __x86_64__ */

/* Convert a native/host siginfo object, into/from the siginfo in the
   layout of the inferiors' architecture.  Returns true if any
   conversion was done; false otherwise.  If DIRECTION is 1, then copy
   from INF to NATIVE.  If DIRECTION is 0, copy from NATIVE to
   INF.  */

static int
x86_siginfo_fixup (siginfo_t *native, void *inf, int direction)
{
#ifdef __x86_64__
  /* Is the inferior 32-bit?  If so, then fixup the siginfo object.  */
  if (register_size (0) == 4)
    {
      if (sizeof (siginfo_t) != sizeof (compat_siginfo_t))
	fatal ("unexpected difference in siginfo");

      if (direction == 0)
	compat_siginfo_from_siginfo ((struct compat_siginfo *) inf, native);
      else
	siginfo_from_compat_siginfo (native, (struct compat_siginfo *) inf);

      return 1;
    }
#endif

  return 0;
}

static int use_xml;

/* Update gdbserver_xmltarget.  */

static void
x86_linux_update_xmltarget (void)
{
  int pid;
  struct regset_info *regset;
  static unsigned long long xcr0;
  static int have_ptrace_getregset = -1;
#if !defined(__x86_64__) && defined(HAVE_PTRACE_GETFPXREGS)
  static int have_ptrace_getfpxregs = -1;
#endif

  if (!current_inferior)
    return;

  /* Before changing the register cache internal layout or the target
     regsets, flush the contents of the current valid caches back to
     the threads.  */
  regcache_invalidate ();

  pid = pid_of (get_thread_lwp (current_inferior));
#ifdef __x86_64__
  if (num_xmm_registers == 8)
    init_registers_i386_linux ();
  else
    init_registers_amd64_linux ();
#else
    {
# ifdef HAVE_PTRACE_GETFPXREGS
      if (have_ptrace_getfpxregs == -1)
	{
	  elf_fpxregset_t fpxregs;

	  if (ptrace (PTRACE_GETFPXREGS, pid, 0, (PTRACE_ARG4_TYPE) &fpxregs) < 0)
	    {
	      have_ptrace_getfpxregs = 0;
	      x86_xcr0 = I386_XSTATE_X87_MASK;

	      /* Disable PTRACE_GETFPXREGS.  */
	      for (regset = target_regsets;
		   regset->fill_function != NULL; regset++)
		if (regset->get_request == PTRACE_GETFPXREGS)
		  {
		    regset->size = 0;
		    break;
		  }
	    }
	  else
	    have_ptrace_getfpxregs = 1;
	}

      if (!have_ptrace_getfpxregs)
	{
	  init_registers_i386_mmx_linux ();
	  return;
	}
# endif
      init_registers_i386_linux ();
    }
#endif

  if (!use_xml)
    {
      /* Don't use XML.  */
#ifdef __x86_64__
      if (num_xmm_registers == 8)
	gdbserver_xmltarget = xmltarget_i386_linux_no_xml;
      else
	gdbserver_xmltarget = xmltarget_amd64_linux_no_xml;
#else
      gdbserver_xmltarget = xmltarget_i386_linux_no_xml;
#endif

      x86_xcr0 = I386_XSTATE_SSE_MASK;

      return;
    }

  /* Check if XSAVE extended state is supported.  */
  if (have_ptrace_getregset == -1)
    {
      unsigned long long xstateregs[I386_XSTATE_SSE_SIZE / sizeof (long long)];
      struct iovec iov;

      iov.iov_base = xstateregs;
      iov.iov_len = sizeof (xstateregs);

      /* Check if PTRACE_GETREGSET works.  */
      if (ptrace (PTRACE_GETREGSET, pid, (PTRACE_ARG3_TYPE) NT_X86_XSTATE,
		  &iov) < 0)
	{
	  have_ptrace_getregset = 0;
	  return;
	}
      else
	have_ptrace_getregset = 1;

      /* Get XCR0 from XSAVE extended state at byte 464.  */
      xcr0 = xstateregs[464 / sizeof (long long)];

      /* Use PTRACE_GETREGSET if it is available.  */
      for (regset = target_regsets;
	   regset->fill_function != NULL; regset++)
	if (regset->get_request == PTRACE_GETREGSET)
	  regset->size = I386_XSTATE_SIZE (xcr0);
	else if (regset->type != GENERAL_REGS)
	  regset->size = 0;
    }

  if (have_ptrace_getregset)
    {
      /* AVX is the highest feature we support.  */
      if ((xcr0 & I386_XSTATE_AVX_MASK) == I386_XSTATE_AVX_MASK)
	{
	  x86_xcr0 = xcr0;

#ifdef __x86_64__
	  /* I386 has 8 xmm regs.  */
	  if (num_xmm_registers == 8)
	    init_registers_i386_avx_linux ();
	  else
	    init_registers_amd64_avx_linux ();
#else
	  init_registers_i386_avx_linux ();
#endif
	}
    }
}

/* Process qSupported query, "xmlRegisters=".  Update the buffer size for
   PTRACE_GETREGSET.  */

static void
x86_linux_process_qsupported (const char *query)
{
  /* Return if gdb doesn't support XML.  If gdb sends "xmlRegisters="
     with "i386" in qSupported query, it supports x86 XML target
     descriptions.  */
  use_xml = 0;
  if (query != NULL && strncmp (query, "xmlRegisters=", 13) == 0)
    {
      char *copy = xstrdup (query + 13);
      char *p;

      for (p = strtok (copy, ","); p != NULL; p = strtok (NULL, ","))
	{
	  if (strcmp (p, "i386") == 0)
	    {
	      use_xml = 1;
	      break;
	    }
	} 

      free (copy);
    }

  x86_linux_update_xmltarget ();
}

/* Initialize gdbserver for the architecture of the inferior.  */

static void
x86_arch_setup (void)
{
#ifdef __x86_64__
  int pid = pid_of (get_thread_lwp (current_inferior));
  char *file = linux_child_pid_to_exec_file (pid);
  int use_64bit = elf_64_file_p (file);

  free (file);

  if (use_64bit < 0)
    {
      /* This can only happen if /proc/<pid>/exe is unreadable,
	 but "that can't happen" if we've gotten this far.
	 Fall through and assume this is a 32-bit program.  */
    }
  else if (use_64bit)
    {
      /* Amd64 doesn't have HAVE_LINUX_USRREGS.  */
      the_low_target.num_regs = -1;
      the_low_target.regmap = NULL;
      the_low_target.cannot_fetch_register = NULL;
      the_low_target.cannot_store_register = NULL;

      /* Amd64 has 16 xmm regs.  */
      num_xmm_registers = 16;

      x86_linux_update_xmltarget ();
      return;
    }
#endif

  /* Ok we have a 32-bit inferior.  */

  the_low_target.num_regs = I386_NUM_REGS;
  the_low_target.regmap = i386_regmap;
  the_low_target.cannot_fetch_register = i386_cannot_fetch_register;
  the_low_target.cannot_store_register = i386_cannot_store_register;

  /* I386 has 8 xmm regs.  */
  num_xmm_registers = 8;

  x86_linux_update_xmltarget ();
}

static int
x86_supports_tracepoints (void)
{
  return 1;
}

static void
append_insns (CORE_ADDR *to, size_t len, const unsigned char *buf)
{
  write_inferior_memory (*to, buf, len);
  *to += len;
}

static int
push_opcode (unsigned char *buf, char *op)
{
  unsigned char *buf_org = buf;

  while (1)
    {
      char *endptr;
      unsigned long ul = strtoul (op, &endptr, 16);

      if (endptr == op)
	break;

      *buf++ = ul;
      op = endptr;
    }

  return buf - buf_org;
}

#ifdef __x86_64__

/* Build a jump pad that saves registers and calls a collection
   function.  Writes a jump instruction to the jump pad to
   JJUMPAD_INSN.  The caller is responsible to write it in at the
   tracepoint address.  */

static int
amd64_install_fast_tracepoint_jump_pad (CORE_ADDR tpoint, CORE_ADDR tpaddr,
					CORE_ADDR collector,
					CORE_ADDR lockaddr,
					ULONGEST orig_size,
					CORE_ADDR *jump_entry,
					unsigned char *jjump_pad_insn,
					ULONGEST *jjump_pad_insn_size,
					CORE_ADDR *adjusted_insn_addr,
					CORE_ADDR *adjusted_insn_addr_end)
{
  unsigned char buf[40];
  int i, offset;
  CORE_ADDR buildaddr = *jump_entry;

  /* Build the jump pad.  */

  /* First, do tracepoint data collection.  Save registers.  */
  i = 0;
  /* Need to ensure stack pointer saved first.  */
  buf[i++] = 0x54; /* push %rsp */
  buf[i++] = 0x55; /* push %rbp */
  buf[i++] = 0x57; /* push %rdi */
  buf[i++] = 0x56; /* push %rsi */
  buf[i++] = 0x52; /* push %rdx */
  buf[i++] = 0x51; /* push %rcx */
  buf[i++] = 0x53; /* push %rbx */
  buf[i++] = 0x50; /* push %rax */
  buf[i++] = 0x41; buf[i++] = 0x57; /* push %r15 */
  buf[i++] = 0x41; buf[i++] = 0x56; /* push %r14 */
  buf[i++] = 0x41; buf[i++] = 0x55; /* push %r13 */
  buf[i++] = 0x41; buf[i++] = 0x54; /* push %r12 */
  buf[i++] = 0x41; buf[i++] = 0x53; /* push %r11 */
  buf[i++] = 0x41; buf[i++] = 0x52; /* push %r10 */
  buf[i++] = 0x41; buf[i++] = 0x51; /* push %r9 */
  buf[i++] = 0x41; buf[i++] = 0x50; /* push %r8 */
  buf[i++] = 0x9c; /* pushfq */
  buf[i++] = 0x48; /* movl <addr>,%rdi */
  buf[i++] = 0xbf;
  *((unsigned long *)(buf + i)) = (unsigned long) tpaddr;
  i += sizeof (unsigned long);
  buf[i++] = 0x57; /* push %rdi */
  append_insns (&buildaddr, i, buf);

  /* Stack space for the collecting_t object.  */
  i = 0;
  i += push_opcode (&buf[i], "48 83 ec 18");	/* sub $0x18,%rsp */
  i += push_opcode (&buf[i], "48 b8");          /* mov <tpoint>,%rax */
  memcpy (buf + i, &tpoint, 8);
  i += 8;
  i += push_opcode (&buf[i], "48 89 04 24");    /* mov %rax,(%rsp) */
  i += push_opcode (&buf[i],
		    "64 48 8b 04 25 00 00 00 00"); /* mov %fs:0x0,%rax */
  i += push_opcode (&buf[i], "48 89 44 24 08"); /* mov %rax,0x8(%rsp) */
  append_insns (&buildaddr, i, buf);

  /* spin-lock.  */
  i = 0;
  i += push_opcode (&buf[i], "48 be");		/* movl <lockaddr>,%rsi */
  memcpy (&buf[i], (void *) &lockaddr, 8);
  i += 8;
  i += push_opcode (&buf[i], "48 89 e1");       /* mov %rsp,%rcx */
  i += push_opcode (&buf[i], "31 c0");		/* xor %eax,%eax */
  i += push_opcode (&buf[i], "f0 48 0f b1 0e"); /* lock cmpxchg %rcx,(%rsi) */
  i += push_opcode (&buf[i], "48 85 c0");	/* test %rax,%rax */
  i += push_opcode (&buf[i], "75 f4");		/* jne <again> */
  append_insns (&buildaddr, i, buf);

  /* Set up the gdb_collect call.  */
  /* At this point, (stack pointer + 0x18) is the base of our saved
     register block.  */

  i = 0;
  i += push_opcode (&buf[i], "48 89 e6");	/* mov %rsp,%rsi */
  i += push_opcode (&buf[i], "48 83 c6 18");	/* add $0x18,%rsi */

  /* tpoint address may be 64-bit wide.  */
  i += push_opcode (&buf[i], "48 bf");		/* movl <addr>,%rdi */
  memcpy (buf + i, &tpoint, 8);
  i += 8;
  append_insns (&buildaddr, i, buf);

  /* The collector function being in the shared library, may be
     >31-bits away off the jump pad.  */
  i = 0;
  i += push_opcode (&buf[i], "48 b8");          /* mov $collector,%rax */
  memcpy (buf + i, &collector, 8);
  i += 8;
  i += push_opcode (&buf[i], "ff d0");          /* callq *%rax */
  append_insns (&buildaddr, i, buf);

  /* Clear the spin-lock.  */
  i = 0;
  i += push_opcode (&buf[i], "31 c0");		/* xor %eax,%eax */
  i += push_opcode (&buf[i], "48 a3");		/* mov %rax, lockaddr */
  memcpy (buf + i, &lockaddr, 8);
  i += 8;
  append_insns (&buildaddr, i, buf);

  /* Remove stack that had been used for the collect_t object.  */
  i = 0;
  i += push_opcode (&buf[i], "48 83 c4 18");	/* add $0x18,%rsp */
  append_insns (&buildaddr, i, buf);

  /* Restore register state.  */
  i = 0;
  buf[i++] = 0x48; /* add $0x8,%rsp */
  buf[i++] = 0x83;
  buf[i++] = 0xc4;
  buf[i++] = 0x08;
  buf[i++] = 0x9d; /* popfq */
  buf[i++] = 0x41; buf[i++] = 0x58; /* pop %r8 */
  buf[i++] = 0x41; buf[i++] = 0x59; /* pop %r9 */
  buf[i++] = 0x41; buf[i++] = 0x5a; /* pop %r10 */
  buf[i++] = 0x41; buf[i++] = 0x5b; /* pop %r11 */
  buf[i++] = 0x41; buf[i++] = 0x5c; /* pop %r12 */
  buf[i++] = 0x41; buf[i++] = 0x5d; /* pop %r13 */
  buf[i++] = 0x41; buf[i++] = 0x5e; /* pop %r14 */
  buf[i++] = 0x41; buf[i++] = 0x5f; /* pop %r15 */
  buf[i++] = 0x58; /* pop %rax */
  buf[i++] = 0x5b; /* pop %rbx */
  buf[i++] = 0x59; /* pop %rcx */
  buf[i++] = 0x5a; /* pop %rdx */
  buf[i++] = 0x5e; /* pop %rsi */
  buf[i++] = 0x5f; /* pop %rdi */
  buf[i++] = 0x5d; /* pop %rbp */
  buf[i++] = 0x5c; /* pop %rsp */
  append_insns (&buildaddr, i, buf);

  /* Now, adjust the original instruction to execute in the jump
     pad.  */
  *adjusted_insn_addr = buildaddr;
  relocate_instruction (&buildaddr, tpaddr);
  *adjusted_insn_addr_end = buildaddr;

  /* Finally, write a jump back to the program.  */
  offset = (tpaddr + orig_size) - (buildaddr + sizeof (jump_insn));
  memcpy (buf, jump_insn, sizeof (jump_insn));
  memcpy (buf + 1, &offset, 4);
  append_insns (&buildaddr, sizeof (jump_insn), buf);

  /* The jump pad is now built.  Wire in a jump to our jump pad.  This
     is always done last (by our caller actually), so that we can
     install fast tracepoints with threads running.  This relies on
     the agent's atomic write support.  */
  offset = *jump_entry - (tpaddr + sizeof (jump_insn));
  memcpy (buf, jump_insn, sizeof (jump_insn));
  memcpy (buf + 1, &offset, 4);
  memcpy (jjump_pad_insn, buf, sizeof (jump_insn));
  *jjump_pad_insn_size = sizeof (jump_insn);

  /* Return the end address of our pad.  */
  *jump_entry = buildaddr;

  return 0;
}

#endif /* __x86_64__ */

/* Build a jump pad that saves registers and calls a collection
   function.  Writes a jump instruction to the jump pad to
   JJUMPAD_INSN.  The caller is responsible to write it in at the
   tracepoint address.  */

static int
i386_install_fast_tracepoint_jump_pad (CORE_ADDR tpoint, CORE_ADDR tpaddr,
				       CORE_ADDR collector,
				       CORE_ADDR lockaddr,
				       ULONGEST orig_size,
				       CORE_ADDR *jump_entry,
				       unsigned char *jjump_pad_insn,
				       ULONGEST *jjump_pad_insn_size,
				       CORE_ADDR *adjusted_insn_addr,
				       CORE_ADDR *adjusted_insn_addr_end)
{
  unsigned char buf[0x100];
  int i, offset;
  CORE_ADDR buildaddr = *jump_entry;

  /* Build the jump pad.  */

  /* First, do tracepoint data collection.  Save registers.  */
  i = 0;
  buf[i++] = 0x60; /* pushad */
  buf[i++] = 0x68; /* push tpaddr aka $pc */
  *((int *)(buf + i)) = (int) tpaddr;
  i += 4;
  buf[i++] = 0x9c; /* pushf */
  buf[i++] = 0x1e; /* push %ds */
  buf[i++] = 0x06; /* push %es */
  buf[i++] = 0x0f; /* push %fs */
  buf[i++] = 0xa0;
  buf[i++] = 0x0f; /* push %gs */
  buf[i++] = 0xa8;
  buf[i++] = 0x16; /* push %ss */
  buf[i++] = 0x0e; /* push %cs */
  append_insns (&buildaddr, i, buf);

  /* Stack space for the collecting_t object.  */
  i = 0;
  i += push_opcode (&buf[i], "83 ec 08");	/* sub    $0x8,%esp */

  /* Build the object.  */
  i += push_opcode (&buf[i], "b8");		/* mov    <tpoint>,%eax */
  memcpy (buf + i, &tpoint, 4);
  i += 4;
  i += push_opcode (&buf[i], "89 04 24");	   /* mov %eax,(%esp) */

  i += push_opcode (&buf[i], "65 a1 00 00 00 00"); /* mov %gs:0x0,%eax */
  i += push_opcode (&buf[i], "89 44 24 04");	   /* mov %eax,0x4(%esp) */
  append_insns (&buildaddr, i, buf);

  /* spin-lock.  Note this is using cmpxchg, which leaves i386 behind.
     If we cared for it, this could be using xchg alternatively.  */

  i = 0;
  i += push_opcode (&buf[i], "31 c0");		/* xor %eax,%eax */
  i += push_opcode (&buf[i], "f0 0f b1 25");    /* lock cmpxchg
						   %esp,<lockaddr> */
  memcpy (&buf[i], (void *) &lockaddr, 4);
  i += 4;
  i += push_opcode (&buf[i], "85 c0");		/* test %eax,%eax */
  i += push_opcode (&buf[i], "75 f2");		/* jne <again> */
  append_insns (&buildaddr, i, buf);


  /* Set up arguments to the gdb_collect call.  */
  i = 0;
  i += push_opcode (&buf[i], "89 e0");		/* mov %esp,%eax */
  i += push_opcode (&buf[i], "83 c0 08");	/* add $0x08,%eax */
  i += push_opcode (&buf[i], "89 44 24 fc");	/* mov %eax,-0x4(%esp) */
  append_insns (&buildaddr, i, buf);

  i = 0;
  i += push_opcode (&buf[i], "83 ec 08");	/* sub $0x8,%esp */
  append_insns (&buildaddr, i, buf);

  i = 0;
  i += push_opcode (&buf[i], "c7 04 24");       /* movl <addr>,(%esp) */
  memcpy (&buf[i], (void *) &tpoint, 4);
  i += 4;
  append_insns (&buildaddr, i, buf);

  buf[0] = 0xe8; /* call <reladdr> */
  offset = collector - (buildaddr + sizeof (jump_insn));
  memcpy (buf + 1, &offset, 4);
  append_insns (&buildaddr, 5, buf);
  /* Clean up after the call.  */
  buf[0] = 0x83; /* add $0x8,%esp */
  buf[1] = 0xc4;
  buf[2] = 0x08;
  append_insns (&buildaddr, 3, buf);


  /* Clear the spin-lock.  This would need the LOCK prefix on older
     broken archs.  */
  i = 0;
  i += push_opcode (&buf[i], "31 c0");		/* xor %eax,%eax */
  i += push_opcode (&buf[i], "a3");		/* mov %eax, lockaddr */
  memcpy (buf + i, &lockaddr, 4);
  i += 4;
  append_insns (&buildaddr, i, buf);


  /* Remove stack that had been used for the collect_t object.  */
  i = 0;
  i += push_opcode (&buf[i], "83 c4 08");	/* add $0x08,%esp */
  append_insns (&buildaddr, i, buf);

  i = 0;
  buf[i++] = 0x83; /* add $0x4,%esp (no pop of %cs, assume unchanged) */
  buf[i++] = 0xc4;
  buf[i++] = 0x04;
  buf[i++] = 0x17; /* pop %ss */
  buf[i++] = 0x0f; /* pop %gs */
  buf[i++] = 0xa9;
  buf[i++] = 0x0f; /* pop %fs */
  buf[i++] = 0xa1;
  buf[i++] = 0x07; /* pop %es */
  buf[i++] = 0x1f; /* pop %de */
  buf[i++] = 0x9d; /* popf */
  buf[i++] = 0x83; /* add $0x4,%esp (pop of tpaddr aka $pc) */
  buf[i++] = 0xc4;
  buf[i++] = 0x04;
  buf[i++] = 0x61; /* popad */
  append_insns (&buildaddr, i, buf);

  /* Now, adjust the original instruction to execute in the jump
     pad.  */
  *adjusted_insn_addr = buildaddr;
  relocate_instruction (&buildaddr, tpaddr);
  *adjusted_insn_addr_end = buildaddr;

  /* Write the jump back to the program.  */
  offset = (tpaddr + orig_size) - (buildaddr + sizeof (jump_insn));
  memcpy (buf, jump_insn, sizeof (jump_insn));
  memcpy (buf + 1, &offset, 4);
  append_insns (&buildaddr, sizeof (jump_insn), buf);

  /* The jump pad is now built.  Wire in a jump to our jump pad.  This
     is always done last (by our caller actually), so that we can
     install fast tracepoints with threads running.  This relies on
     the agent's atomic write support.  */
  offset = *jump_entry - (tpaddr + sizeof (jump_insn));
  memcpy (buf, jump_insn, sizeof (jump_insn));
  memcpy (buf + 1, &offset, 4);
  memcpy (jjump_pad_insn, buf, sizeof (jump_insn));
  *jjump_pad_insn_size = sizeof (jump_insn);

  /* Return the end address of our pad.  */
  *jump_entry = buildaddr;

  return 0;
}

static int
x86_install_fast_tracepoint_jump_pad (CORE_ADDR tpoint, CORE_ADDR tpaddr,
				      CORE_ADDR collector,
				      CORE_ADDR lockaddr,
				      ULONGEST orig_size,
				      CORE_ADDR *jump_entry,
				      unsigned char *jjump_pad_insn,
				      ULONGEST *jjump_pad_insn_size,
				      CORE_ADDR *adjusted_insn_addr,
				      CORE_ADDR *adjusted_insn_addr_end)
{
#ifdef __x86_64__
  if (register_size (0) == 8)
    return amd64_install_fast_tracepoint_jump_pad (tpoint, tpaddr,
						   collector, lockaddr,
						   orig_size, jump_entry,
						   jjump_pad_insn,
						   jjump_pad_insn_size,
						   adjusted_insn_addr,
						   adjusted_insn_addr_end);
#endif

  return i386_install_fast_tracepoint_jump_pad (tpoint, tpaddr,
						collector, lockaddr,
						orig_size, jump_entry,
						jjump_pad_insn,
						jjump_pad_insn_size,
						adjusted_insn_addr,
						adjusted_insn_addr_end);
}

static void
add_insns (unsigned char *start, int len)
{
  CORE_ADDR buildaddr = current_insn_ptr;

  if (debug_threads)
    fprintf (stderr, "Adding %d bytes of insn at %s\n",
	     len, paddress (buildaddr));

  append_insns (&buildaddr, len, start);
  current_insn_ptr = buildaddr;
}

/* Our general strategy for emitting code is to avoid specifying raw
   bytes whenever possible, and instead copy a block of inline asm
   that is embedded in the function.  This is a little messy, because
   we need to keep the compiler from discarding what looks like dead
   code, plus suppress various warnings.  */

#define EMIT_ASM(NAME, INSNS)						\
  do									\
    {									\
      extern unsigned char start_ ## NAME, end_ ## NAME;		\
      add_insns (&start_ ## NAME, &end_ ## NAME - &start_ ## NAME);	\
      __asm__ ("jmp end_" #NAME "\n"					\
	       "\t" "start_" #NAME ":"					\
	       "\t" INSNS "\n"						\
	       "\t" "end_" #NAME ":");					\
    } while (0)

#ifdef __x86_64__

#define EMIT_ASM32(NAME,INSNS)						\
  do									\
    {									\
      extern unsigned char start_ ## NAME, end_ ## NAME;		\
      add_insns (&start_ ## NAME, &end_ ## NAME - &start_ ## NAME);	\
      __asm__ (".code32\n"						\
	       "\t" "jmp end_" #NAME "\n"				\
	       "\t" "start_" #NAME ":\n"				\
	       "\t" INSNS "\n"						\
	       "\t" "end_" #NAME ":\n"					\
	       ".code64\n");						\
    } while (0)

#else

#define EMIT_ASM32(NAME,INSNS) EMIT_ASM(NAME,INSNS)

#endif

#ifdef __x86_64__

static void
amd64_emit_prologue (void)
{
  EMIT_ASM (amd64_prologue,
	    "pushq %rbp\n\t"
	    "movq %rsp,%rbp\n\t"
	    "sub $0x20,%rsp\n\t"
	    "movq %rdi,-8(%rbp)\n\t"
	    "movq %rsi,-16(%rbp)");
}


static void
amd64_emit_epilogue (void)
{
  EMIT_ASM (amd64_epilogue,
	    "movq -16(%rbp),%rdi\n\t"
	    "movq %rax,(%rdi)\n\t"
	    "xor %rax,%rax\n\t"
	    "leave\n\t"
	    "ret");
}

static void
amd64_emit_add (void)
{
  EMIT_ASM (amd64_add,
	    "add (%rsp),%rax\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_sub (void)
{
  EMIT_ASM (amd64_sub,
	    "sub %rax,(%rsp)\n\t"
	    "pop %rax");
}

static void
amd64_emit_mul (void)
{
  emit_error = 1;
}

static void
amd64_emit_lsh (void)
{
  emit_error = 1;
}

static void
amd64_emit_rsh_signed (void)
{
  emit_error = 1;
}

static void
amd64_emit_rsh_unsigned (void)
{
  emit_error = 1;
}

static void
amd64_emit_ext (int arg)
{
  switch (arg)
    {
    case 8:
      EMIT_ASM (amd64_ext_8,
		"cbtw\n\t"
		"cwtl\n\t"
		"cltq");
      break;
    case 16:
      EMIT_ASM (amd64_ext_16,
		"cwtl\n\t"
		"cltq");
      break;
    case 32:
      EMIT_ASM (amd64_ext_32,
		"cltq");
      break;
    default:
      emit_error = 1;
    }
}

static void
amd64_emit_log_not (void)
{
  EMIT_ASM (amd64_log_not,
	    "test %rax,%rax\n\t"
	    "sete %cl\n\t"
	    "movzbq %cl,%rax");
}

static void
amd64_emit_bit_and (void)
{
  EMIT_ASM (amd64_and,
	    "and (%rsp),%rax\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_bit_or (void)
{
  EMIT_ASM (amd64_or,
	    "or (%rsp),%rax\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_bit_xor (void)
{
  EMIT_ASM (amd64_xor,
	    "xor (%rsp),%rax\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_bit_not (void)
{
  EMIT_ASM (amd64_bit_not,
	    "xorq $0xffffffffffffffff,%rax");
}

static void
amd64_emit_equal (void)
{
  EMIT_ASM (amd64_equal,
	    "cmp %rax,(%rsp)\n\t"
	    "je .Lamd64_equal_true\n\t"
	    "xor %rax,%rax\n\t"
	    "jmp .Lamd64_equal_end\n\t"
	    ".Lamd64_equal_true:\n\t"
	    "mov $0x1,%rax\n\t"
	    ".Lamd64_equal_end:\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_less_signed (void)
{
  EMIT_ASM (amd64_less_signed,
	    "cmp %rax,(%rsp)\n\t"
	    "jl .Lamd64_less_signed_true\n\t"
	    "xor %rax,%rax\n\t"
	    "jmp .Lamd64_less_signed_end\n\t"
	    ".Lamd64_less_signed_true:\n\t"
	    "mov $1,%rax\n\t"
	    ".Lamd64_less_signed_end:\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_less_unsigned (void)
{
  EMIT_ASM (amd64_less_unsigned,
	    "cmp %rax,(%rsp)\n\t"
	    "jb .Lamd64_less_unsigned_true\n\t"
	    "xor %rax,%rax\n\t"
	    "jmp .Lamd64_less_unsigned_end\n\t"
	    ".Lamd64_less_unsigned_true:\n\t"
	    "mov $1,%rax\n\t"
	    ".Lamd64_less_unsigned_end:\n\t"
	    "lea 0x8(%rsp),%rsp");
}

static void
amd64_emit_ref (int size)
{
  switch (size)
    {
    case 1:
      EMIT_ASM (amd64_ref1,
		"movb (%rax),%al");
      break;
    case 2:
      EMIT_ASM (amd64_ref2,
		"movw (%rax),%ax");
      break;
    case 4:
      EMIT_ASM (amd64_ref4,
		"movl (%rax),%eax");
      break;
    case 8:
      EMIT_ASM (amd64_ref8,
		"movq (%rax),%rax");
      break;
    }
}

static void
amd64_emit_if_goto (int *offset_p, int *size_p)
{
  EMIT_ASM (amd64_if_goto,
	    "mov %rax,%rcx\n\t"
	    "pop %rax\n\t"
	    "cmp $0,%rcx\n\t"
	    ".byte 0x0f, 0x85, 0x0, 0x0, 0x0, 0x0");
  if (offset_p)
    *offset_p = 10;
  if (size_p)
    *size_p = 4;
}

static void
amd64_emit_goto (int *offset_p, int *size_p)
{
  EMIT_ASM (amd64_goto,
	    ".byte 0xe9, 0x0, 0x0, 0x0, 0x0");
  if (offset_p)
    *offset_p = 1;
  if (size_p)
    *size_p = 4;
}

static void
amd64_write_goto_address (CORE_ADDR from, CORE_ADDR to, int size)
{
  int diff = (to - (from + size));
  unsigned char buf[sizeof (int)];

  if (size != 4)
    {
      emit_error = 1;
      return;
    }

  memcpy (buf, &diff, sizeof (int));
  write_inferior_memory (from, buf, sizeof (int));
}

static void
amd64_emit_const (LONGEST num)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr = current_insn_ptr;

  i = 0;
  buf[i++] = 0x48;  buf[i++] = 0xb8; /* mov $<n>,%rax */
  memcpy (&buf[i], &num, sizeof (num));
  i += 8;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
}

static void
amd64_emit_call (CORE_ADDR fn)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;
  LONGEST offset64;

  /* The destination function being in the shared library, may be
     >31-bits away off the compiled code pad.  */

  buildaddr = current_insn_ptr;

  offset64 = fn - (buildaddr + 1 /* call op */ + 4 /* 32-bit offset */);

  i = 0;

  if (offset64 > INT_MAX || offset64 < INT_MIN)
    {
      /* Offset is too large for a call.  Use callq, but that requires
	 a register, so avoid it if possible.  Use r10, since it is
	 call-clobbered, we don't have to push/pop it.  */
      buf[i++] = 0x48; /* mov $fn,%r10 */
      buf[i++] = 0xba;
      memcpy (buf + i, &fn, 8);
      i += 8;
      buf[i++] = 0xff; /* callq *%r10 */
      buf[i++] = 0xd2;
    }
  else
    {
      int offset32 = offset64; /* we know we can't overflow here.  */
      memcpy (buf + i, &offset32, 4);
      i += 4;
    }

  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
}

static void
amd64_emit_reg (int reg)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  /* Assume raw_regs is still in %rdi.  */
  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xbe; /* mov $<n>,%esi */
  memcpy (&buf[i], &reg, sizeof (reg));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  amd64_emit_call (get_raw_reg_func_addr ());
}

static void
amd64_emit_pop (void)
{
  EMIT_ASM (amd64_pop,
	    "pop %rax");
}

static void
amd64_emit_stack_flush (void)
{
  EMIT_ASM (amd64_stack_flush,
	    "push %rax");
}

static void
amd64_emit_zero_ext (int arg)
{
  switch (arg)
    {
    case 8:
      EMIT_ASM (amd64_zero_ext_8,
		"and $0xff,%rax");
      break;
    case 16:
      EMIT_ASM (amd64_zero_ext_16,
		"and $0xffff,%rax");
      break;
    case 32:
      EMIT_ASM (amd64_zero_ext_32,
		"mov $0xffffffff,%rcx\n\t"
		"and %rcx,%rax");
      break;
    default:
      emit_error = 1;
    }
}

static void
amd64_emit_swap (void)
{
  EMIT_ASM (amd64_swap,
	    "mov %rax,%rcx\n\t"
	    "pop %rax\n\t"
	    "push %rcx");
}

static void
amd64_emit_stack_adjust (int n)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr = current_insn_ptr;

  i = 0;
  buf[i++] = 0x48; /* lea $<n>(%rsp),%rsp */
  buf[i++] = 0x8d;
  buf[i++] = 0x64;
  buf[i++] = 0x24;
  /* This only handles adjustments up to 16, but we don't expect any more.  */
  buf[i++] = n * 8;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
}

/* FN's prototype is `LONGEST(*fn)(int)'.  */

static void
amd64_emit_int_call_1 (CORE_ADDR fn, int arg1)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xbf; /* movl $<n>,%edi */
  memcpy (&buf[i], &arg1, sizeof (arg1));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  amd64_emit_call (fn);
}

/* FN's prototype is `void(*fn)(int,LONGEST)'.  */

static void
amd64_emit_void_call_2 (CORE_ADDR fn, int arg1)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xbf; /* movl $<n>,%edi */
  memcpy (&buf[i], &arg1, sizeof (arg1));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  EMIT_ASM (amd64_void_call_2_a,
	    /* Save away a copy of the stack top.  */
	    "push %rax\n\t"
	    /* Also pass top as the second argument.  */
	    "mov %rax,%rsi");
  amd64_emit_call (fn);
  EMIT_ASM (amd64_void_call_2_b,
	    /* Restore the stack top, %rax may have been trashed.  */
	    "pop %rax");
}

struct emit_ops amd64_emit_ops =
  {
    amd64_emit_prologue,
    amd64_emit_epilogue,
    amd64_emit_add,
    amd64_emit_sub,
    amd64_emit_mul,
    amd64_emit_lsh,
    amd64_emit_rsh_signed,
    amd64_emit_rsh_unsigned,
    amd64_emit_ext,
    amd64_emit_log_not,
    amd64_emit_bit_and,
    amd64_emit_bit_or,
    amd64_emit_bit_xor,
    amd64_emit_bit_not,
    amd64_emit_equal,
    amd64_emit_less_signed,
    amd64_emit_less_unsigned,
    amd64_emit_ref,
    amd64_emit_if_goto,
    amd64_emit_goto,
    amd64_write_goto_address,
    amd64_emit_const,
    amd64_emit_call,
    amd64_emit_reg,
    amd64_emit_pop,
    amd64_emit_stack_flush,
    amd64_emit_zero_ext,
    amd64_emit_swap,
    amd64_emit_stack_adjust,
    amd64_emit_int_call_1,
    amd64_emit_void_call_2
  };

#endif /* __x86_64__ */

static void
i386_emit_prologue (void)
{
  EMIT_ASM32 (i386_prologue,
	    "push %ebp\n\t"
	    "mov %esp,%ebp");
  /* At this point, the raw regs base address is at 8(%ebp), and the
     value pointer is at 12(%ebp).  */
}

static void
i386_emit_epilogue (void)
{
  EMIT_ASM32 (i386_epilogue,
	    "mov 12(%ebp),%ecx\n\t"
	    "mov %eax,(%ecx)\n\t"
	    "mov %ebx,0x4(%ecx)\n\t"
	    "xor %eax,%eax\n\t"
	    "pop %ebp\n\t"
	    "ret");
}

static void
i386_emit_add (void)
{
  EMIT_ASM32 (i386_add,
	    "add (%esp),%eax\n\t"
	    "adc 0x4(%esp),%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_sub (void)
{
  EMIT_ASM32 (i386_sub,
	    "subl %eax,(%esp)\n\t"
	    "sbbl %ebx,4(%esp)\n\t"
	    "pop %eax\n\t"
	    "pop %ebx\n\t");
}

static void
i386_emit_mul (void)
{
  emit_error = 1;
}

static void
i386_emit_lsh (void)
{
  emit_error = 1;
}

static void
i386_emit_rsh_signed (void)
{
  emit_error = 1;
}

static void
i386_emit_rsh_unsigned (void)
{
  emit_error = 1;
}

static void
i386_emit_ext (int arg)
{
  switch (arg)
    {
    case 8:
      EMIT_ASM32 (i386_ext_8,
		"cbtw\n\t"
		"cwtl\n\t"
		"movl %eax,%ebx\n\t"
		"sarl $31,%ebx");
      break;
    case 16:
      EMIT_ASM32 (i386_ext_16,
		"cwtl\n\t"
		"movl %eax,%ebx\n\t"
		"sarl $31,%ebx");
      break;
    case 32:
      EMIT_ASM32 (i386_ext_32,
		"movl %eax,%ebx\n\t"
		"sarl $31,%ebx");
      break;
    default:
      emit_error = 1;
    }
}

static void
i386_emit_log_not (void)
{
  EMIT_ASM32 (i386_log_not,
	    "or %ebx,%eax\n\t"
	    "test %eax,%eax\n\t"
	    "sete %cl\n\t"
	    "xor %ebx,%ebx\n\t"
	    "movzbl %cl,%eax");
}

static void
i386_emit_bit_and (void)
{
  EMIT_ASM32 (i386_and,
	    "and (%esp),%eax\n\t"
	    "and 0x4(%esp),%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_bit_or (void)
{
  EMIT_ASM32 (i386_or,
	    "or (%esp),%eax\n\t"
	    "or 0x4(%esp),%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_bit_xor (void)
{
  EMIT_ASM32 (i386_xor,
	    "xor (%esp),%eax\n\t"
	    "xor 0x4(%esp),%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_bit_not (void)
{
  EMIT_ASM32 (i386_bit_not,
	    "xor $0xffffffff,%eax\n\t"
	    "xor $0xffffffff,%ebx\n\t");
}

static void
i386_emit_equal (void)
{
  EMIT_ASM32 (i386_equal,
	    "cmpl %ebx,4(%esp)\n\t"
	    "jne .Li386_equal_false\n\t"
	    "cmpl %eax,(%esp)\n\t"
	    "je .Li386_equal_true\n\t"
	    ".Li386_equal_false:\n\t"
	    "xor %eax,%eax\n\t"
	    "jmp .Li386_equal_end\n\t"
	    ".Li386_equal_true:\n\t"
	    "mov $1,%eax\n\t"
	    ".Li386_equal_end:\n\t"
	    "xor %ebx,%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_less_signed (void)
{
  EMIT_ASM32 (i386_less_signed,
	    "cmpl %ebx,4(%esp)\n\t"
	    "jl .Li386_less_signed_true\n\t"
	    "jne .Li386_less_signed_false\n\t"
	    "cmpl %eax,(%esp)\n\t"
	    "jl .Li386_less_signed_true\n\t"
	    ".Li386_less_signed_false:\n\t"
	    "xor %eax,%eax\n\t"
	    "jmp .Li386_less_signed_end\n\t"
	    ".Li386_less_signed_true:\n\t"
	    "mov $1,%eax\n\t"
	    ".Li386_less_signed_end:\n\t"
	    "xor %ebx,%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_less_unsigned (void)
{
  EMIT_ASM32 (i386_less_unsigned,
	    "cmpl %ebx,4(%esp)\n\t"
	    "jb .Li386_less_unsigned_true\n\t"
	    "jne .Li386_less_unsigned_false\n\t"
	    "cmpl %eax,(%esp)\n\t"
	    "jb .Li386_less_unsigned_true\n\t"
	    ".Li386_less_unsigned_false:\n\t"
	    "xor %eax,%eax\n\t"
	    "jmp .Li386_less_unsigned_end\n\t"
	    ".Li386_less_unsigned_true:\n\t"
	    "mov $1,%eax\n\t"
	    ".Li386_less_unsigned_end:\n\t"
	    "xor %ebx,%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_ref (int size)
{
  switch (size)
    {
    case 1:
      EMIT_ASM32 (i386_ref1,
		"movb (%eax),%al");
      break;
    case 2:
      EMIT_ASM32 (i386_ref2,
		"movw (%eax),%ax");
      break;
    case 4:
      EMIT_ASM32 (i386_ref4,
		"movl (%eax),%eax");
      break;
    case 8:
      EMIT_ASM32 (i386_ref8,
		"movl 4(%eax),%ebx\n\t"
		"movl (%eax),%eax");
      break;
    }
}

static void
i386_emit_if_goto (int *offset_p, int *size_p)
{
  EMIT_ASM32 (i386_if_goto,
	    "mov %eax,%ecx\n\t"
	    "or %ebx,%ecx\n\t"
	    "pop %eax\n\t"
	    "pop %ebx\n\t"
	    "cmpl $0,%ecx\n\t"
	    /* Don't trust the assembler to choose the right jump */
	    ".byte 0x0f, 0x85, 0x0, 0x0, 0x0, 0x0");

  if (offset_p)
    *offset_p = 11; /* be sure that this matches the sequence above */
  if (size_p)
    *size_p = 4;
}

static void
i386_emit_goto (int *offset_p, int *size_p)
{
  EMIT_ASM32 (i386_goto,
	    /* Don't trust the assembler to choose the right jump */
	    ".byte 0xe9, 0x0, 0x0, 0x0, 0x0");
  if (offset_p)
    *offset_p = 1;
  if (size_p)
    *size_p = 4;
}

static void
i386_write_goto_address (CORE_ADDR from, CORE_ADDR to, int size)
{
  int diff = (to - (from + size));
  unsigned char buf[sizeof (int)];

  /* We're only doing 4-byte sizes at the moment.  */
  if (size != 4)
    {
      emit_error = 1;
      return;
    }

  memcpy (buf, &diff, sizeof (int));
  write_inferior_memory (from, buf, sizeof (int));
}

static void
i386_emit_const (LONGEST num)
{
  unsigned char buf[16];
  int i, hi, lo;
  CORE_ADDR buildaddr = current_insn_ptr;

  i = 0;
  buf[i++] = 0xb8; /* mov $<n>,%eax */
  lo = num & 0xffffffff;
  memcpy (&buf[i], &lo, sizeof (lo));
  i += 4;
  hi = ((num >> 32) & 0xffffffff);
  if (hi)
    {
      buf[i++] = 0xbb; /* mov $<n>,%ebx */
      memcpy (&buf[i], &hi, sizeof (hi));
      i += 4;
    }
  else
    {
      buf[i++] = 0x31; buf[i++] = 0xdb; /* xor %ebx,%ebx */
    }
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
}

static void
i386_emit_call (CORE_ADDR fn)
{
  unsigned char buf[16];
  int i, offset;
  CORE_ADDR buildaddr;

  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xe8; /* call <reladdr> */
  offset = ((int) fn) - (buildaddr + 5);
  memcpy (buf + 1, &offset, 4);
  append_insns (&buildaddr, 5, buf);
  current_insn_ptr = buildaddr;
}

static void
i386_emit_reg (int reg)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  EMIT_ASM32 (i386_reg_a,
	    "sub $0x8,%esp");
  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xb8; /* mov $<n>,%eax */
  memcpy (&buf[i], &reg, sizeof (reg));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  EMIT_ASM32 (i386_reg_b,
	    "mov %eax,4(%esp)\n\t"
	    "mov 8(%ebp),%eax\n\t"
	    "mov %eax,(%esp)");
  i386_emit_call (get_raw_reg_func_addr ());
  EMIT_ASM32 (i386_reg_c,
	    "xor %ebx,%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

static void
i386_emit_pop (void)
{
  EMIT_ASM32 (i386_pop,
	    "pop %eax\n\t"
	    "pop %ebx");
}

static void
i386_emit_stack_flush (void)
{
  EMIT_ASM32 (i386_stack_flush,
	    "push %ebx\n\t"
	    "push %eax");
}

static void
i386_emit_zero_ext (int arg)
{
  switch (arg)
    {
    case 8:
      EMIT_ASM32 (i386_zero_ext_8,
		"and $0xff,%eax\n\t"
		"xor %ebx,%ebx");
      break;
    case 16:
      EMIT_ASM32 (i386_zero_ext_16,
		"and $0xffff,%eax\n\t"
		"xor %ebx,%ebx");
      break;
    case 32:
      EMIT_ASM32 (i386_zero_ext_32,
		"xor %ebx,%ebx");
      break;
    default:
      emit_error = 1;
    }
}

static void
i386_emit_swap (void)
{
  EMIT_ASM32 (i386_swap,
	    "mov %eax,%ecx\n\t"
	    "mov %ebx,%edx\n\t"
	    "pop %eax\n\t"
	    "pop %ebx\n\t"
	    "push %edx\n\t"
	    "push %ecx");
}

static void
i386_emit_stack_adjust (int n)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr = current_insn_ptr;

  i = 0;
  buf[i++] = 0x8d; /* lea $<n>(%esp),%esp */
  buf[i++] = 0x64;
  buf[i++] = 0x24;
  buf[i++] = n * 8;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
}

/* FN's prototype is `LONGEST(*fn)(int)'.  */

static void
i386_emit_int_call_1 (CORE_ADDR fn, int arg1)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  EMIT_ASM32 (i386_int_call_1_a,
	    /* Reserve a bit of stack space.  */
	    "sub $0x8,%esp");
  /* Put the one argument on the stack.  */
  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xc7;  /* movl $<arg1>,(%esp) */
  buf[i++] = 0x04;
  buf[i++] = 0x24;
  memcpy (&buf[i], &arg1, sizeof (arg1));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  i386_emit_call (fn);
  EMIT_ASM32 (i386_int_call_1_c,
	    "mov %edx,%ebx\n\t"
	    "lea 0x8(%esp),%esp");
}

/* FN's prototype is `void(*fn)(int,LONGEST)'.  */

static void
i386_emit_void_call_2 (CORE_ADDR fn, int arg1)
{
  unsigned char buf[16];
  int i;
  CORE_ADDR buildaddr;

  EMIT_ASM32 (i386_void_call_2_a,
	    /* Preserve %eax only; we don't have to worry about %ebx.  */
	    "push %eax\n\t"
	    /* Reserve a bit of stack space for arguments.  */
	    "sub $0x10,%esp\n\t"
	    /* Copy "top" to the second argument position.  (Note that
	       we can't assume function won't scribble on its
	       arguments, so don't try to restore from this.)  */
	    "mov %eax,4(%esp)\n\t"
	    "mov %ebx,8(%esp)");
  /* Put the first argument on the stack.  */
  buildaddr = current_insn_ptr;
  i = 0;
  buf[i++] = 0xc7;  /* movl $<arg1>,(%esp) */
  buf[i++] = 0x04;
  buf[i++] = 0x24;
  memcpy (&buf[i], &arg1, sizeof (arg1));
  i += 4;
  append_insns (&buildaddr, i, buf);
  current_insn_ptr = buildaddr;
  i386_emit_call (fn);
  EMIT_ASM32 (i386_void_call_2_b,
	    "lea 0x10(%esp),%esp\n\t"
	    /* Restore original stack top.  */
	    "pop %eax");
}

struct emit_ops i386_emit_ops =
  {
    i386_emit_prologue,
    i386_emit_epilogue,
    i386_emit_add,
    i386_emit_sub,
    i386_emit_mul,
    i386_emit_lsh,
    i386_emit_rsh_signed,
    i386_emit_rsh_unsigned,
    i386_emit_ext,
    i386_emit_log_not,
    i386_emit_bit_and,
    i386_emit_bit_or,
    i386_emit_bit_xor,
    i386_emit_bit_not,
    i386_emit_equal,
    i386_emit_less_signed,
    i386_emit_less_unsigned,
    i386_emit_ref,
    i386_emit_if_goto,
    i386_emit_goto,
    i386_write_goto_address,
    i386_emit_const,
    i386_emit_call,
    i386_emit_reg,
    i386_emit_pop,
    i386_emit_stack_flush,
    i386_emit_zero_ext,
    i386_emit_swap,
    i386_emit_stack_adjust,
    i386_emit_int_call_1,
    i386_emit_void_call_2
  };


static struct emit_ops *
x86_emit_ops (void)
{
#ifdef __x86_64__
  int use_64bit = register_size (0) == 8;

  if (use_64bit)
    return &amd64_emit_ops;
  else
#endif
    return &i386_emit_ops;
}

/* This is initialized assuming an amd64 target.
   x86_arch_setup will correct it for i386 or amd64 targets.  */

struct linux_target_ops the_low_target =
{
  x86_arch_setup,
  -1,
  NULL,
  NULL,
  NULL,
  x86_get_pc,
  x86_set_pc,
  x86_breakpoint,
  x86_breakpoint_len,
  NULL,
  1,
  x86_breakpoint_at,
  x86_insert_point,
  x86_remove_point,
  x86_stopped_by_watchpoint,
  x86_stopped_data_address,
  /* collect_ptrace_register/supply_ptrace_register are not needed in the
     native i386 case (no registers smaller than an xfer unit), and are not
     used in the biarch case (HAVE_LINUX_USRREGS is not defined).  */
  NULL,
  NULL,
  /* need to fix up i386 siginfo if host is amd64 */
  x86_siginfo_fixup,
  x86_linux_new_process,
  x86_linux_new_thread,
  x86_linux_prepare_to_resume,
  x86_linux_process_qsupported,
  x86_supports_tracepoints,
  x86_get_thread_area,
  x86_install_fast_tracepoint_jump_pad,
  x86_emit_ops
};
