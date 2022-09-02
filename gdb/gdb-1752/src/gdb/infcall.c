/* Perform an inferior function call, for GDB, the GNU debugger.

   Copyright 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994,
   1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005
   Free Software Foundation, Inc.

   This file is part of GDB.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

#include "defs.h"
#include "breakpoint.h"
#include "target.h"
#include "regcache.h"
#include "inferior.h"
#include "gdb_assert.h"
#include "block.h"
#include "gdbcore.h"
#include "language.h"
#include "objfiles.h"
#include "gdbcmd.h"
#include "command.h"
#include "gdb_string.h"
#include "infcall.h"
#include "dummy-frame.h"
#include <sys/time.h>
#include "exceptions.h"
#include "objc-lang.h"
#include "disasm.h"
#include "target.h"
#include "language.h"

/* APPLE LOCAL checkpointing */
extern void begin_inferior_call_checkpoints (void);
extern void end_inferior_call_checkpoints (void);

#if defined (NM_NEXTSTEP)
#include "macosx-nat-infthread.h"

#endif
/* Whether to allow inferior function calls to be made or not.
   e.g. translated processes cannot do inferior function calls (or changing
   the PC in any way) and can terminate the inferior if you try.  
   There is also a set variable you can use to control this if you want to.  */
int inferior_function_calls_disabled_p = 0;

/* APPLE LOCAL: Usually you want to interrupt an inferior function call if it
   is about to raise an ObjC exception.  But somebody might not want to...  */
int objc_exceptions_interrupt_hand_call = 1;

/* APPLE LOCAL: Record the ptid of the thread we are calling functions on.
   If we get more than one exception while calling a function, prefer the
   one that we were hand-calling a function on.  */
ptid_t hand_call_ptid;
ptid_t get_hand_call_ptid ()
{
  return hand_call_ptid;
}

static void 
do_reset_hand_call_ptid ()
{
  hand_call_ptid = minus_one_ptid;
}

static void
do_unset_proceed_from_hand_call (void *unused)
{
  proceed_from_hand_call = 0;
}
/* END APPLE LOCAL  */

/* NOTE: cagney/2003-04-16: What's the future of this code?

   GDB needs an asynchronous expression evaluator, that means an
   asynchronous inferior function call implementation, and that in
   turn means restructuring the code so that it is event driven.  */

/* How you should pass arguments to a function depends on whether it
   was defined in K&R style or prototype style.  If you define a
   function using the K&R syntax that takes a `float' argument, then
   callers must pass that argument as a `double'.  If you define the
   function using the prototype syntax, then you must pass the
   argument as a `float', with no promotion.

   Unfortunately, on certain older platforms, the debug info doesn't
   indicate reliably how each function was defined.  A function type's
   TYPE_FLAG_PROTOTYPED flag may be clear, even if the function was
   defined in prototype style.  When calling a function whose
   TYPE_FLAG_PROTOTYPED flag is clear, GDB consults this flag to
   decide what to do.

   For modern targets, it is proper to assume that, if the prototype
   flag is clear, that can be trusted: `float' arguments should be
   promoted to `double'.  For some older targets, if the prototype
   flag is clear, that doesn't tell us anything.  The default is to
   trust the debug information; the user can override this behavior
   with "set coerce-float-to-double 0".  */

static int coerce_float_to_double_p = 1;
static void
show_coerce_float_to_double_p (struct ui_file *file, int from_tty,
			       struct cmd_list_element *c, const char *value)
{
  fprintf_filtered (file, _("\
Coercion of floats to doubles when calling functions is %s.\n"),
		    value);
}

/* This boolean tells what gdb should do if a signal is received while
   in a function called from gdb (call dummy).  If set, gdb unwinds
   the stack and restore the context to what as it was before the
   call.

   The default is to stop in the frame where the signal was received. */

int unwind_on_signal_p = 0;

int
set_unwind_on_signal (int new_val)
{
  int old_val = unwind_on_signal_p;
  unwind_on_signal_p = new_val;
  return old_val;
}

/* A variant that can be registered with make_cleanup() without any
   sizeof int == sizeof void* assumptions.  */

static void
set_unwind_on_signal_cleanup (void *new_val)
{
  unwind_on_signal_p = (int) new_val;
}

struct cleanup *
make_cleanup_set_restore_unwind_on_signal (int newval)
{
  struct cleanup *cleanup 
    = make_cleanup (set_unwind_on_signal_cleanup, (void *) unwind_on_signal_p);
  unwind_on_signal_p = newval;
  return cleanup;
}

static void
show_unwind_on_signal_p (struct ui_file *file, int from_tty,
			 struct cmd_list_element *c, const char *value)
{
  fprintf_filtered (file, _("\
Unwinding of stack if a signal is received while in a call dummy is %s.\n"),
		    value);
}


/* Perform the standard coercions that are specified
   for arguments to be passed to C functions.

   If PARAM_TYPE is non-NULL, it is the expected parameter type.
   IS_PROTOTYPED is non-zero if the function declaration is prototyped.  */

static struct value *
value_arg_coerce (struct value *arg, struct type *param_type,
		  int is_prototyped)
{
  struct type *arg_type = check_typedef (value_type (arg));
  struct type *type
    = param_type ? check_typedef (param_type) : arg_type;

  switch (TYPE_CODE (type))
    {
    case TYPE_CODE_REF:
      if (TYPE_CODE (arg_type) != TYPE_CODE_REF
	  && TYPE_CODE (arg_type) != TYPE_CODE_PTR)
	{
	  arg = value_addr (arg);
	  deprecated_set_value_type (arg, param_type);
	  return arg;
	}
      break;
    case TYPE_CODE_INT:
    case TYPE_CODE_CHAR:
    case TYPE_CODE_BOOL:
    case TYPE_CODE_ENUM:
      /* If we don't have a prototype, coerce to integer type if necessary.  */
      if (!is_prototyped)
	{
	  if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin_type_int))
	    type = builtin_type_int;
	}
      /* Currently all target ABIs require at least the width of an integer
         type for an argument.  We may have to conditionalize the following
         type coercion for future targets.  */
      if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin_type_int))
	type = builtin_type_int;
      break;
    case TYPE_CODE_FLT:
      if (!is_prototyped && coerce_float_to_double_p)
	{
	  if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin_type_double))
	    type = builtin_type_double;
	  else if (TYPE_LENGTH (type) > TYPE_LENGTH (builtin_type_double))
	    type = builtin_type_long_double;
	}
      break;
    case TYPE_CODE_FUNC:
      type = lookup_pointer_type (type);
      break;
    case TYPE_CODE_ARRAY:
      /* Arrays are coerced to pointers to their first element, unless
         they are vectors, in which case we want to leave them alone,
         because they are passed by value.  */
      if (current_language->c_style_arrays)
	if (!TYPE_VECTOR (type))
	  type = lookup_pointer_type (TYPE_TARGET_TYPE (type));
      break;
    case TYPE_CODE_UNDEF:
    case TYPE_CODE_PTR:
    case TYPE_CODE_STRUCT:
    case TYPE_CODE_UNION:
    case TYPE_CODE_VOID:
    case TYPE_CODE_SET:
    case TYPE_CODE_RANGE:
    case TYPE_CODE_STRING:
    case TYPE_CODE_BITSTRING:
    case TYPE_CODE_ERROR:
    case TYPE_CODE_MEMBERPTR:
    case TYPE_CODE_METHODPTR:
    case TYPE_CODE_METHOD:
    case TYPE_CODE_COMPLEX:
    default:
      break;
    }

  return value_cast (type, arg);
}

/* Determine a function's address and its return type from its value.
   Calls error() if the function is not valid for calling.  */

CORE_ADDR
find_function_addr (struct value *function, struct type **retval_type)
{
  struct type *ftype = check_typedef (value_type (function));
  enum type_code code = TYPE_CODE (ftype);
  struct type *value_type;
  CORE_ADDR funaddr = 0;

  /* If it's a member function, just look at the function
     part of it.  */

  /* Determine address to call.  */
  if (code == TYPE_CODE_FUNC || code == TYPE_CODE_METHOD)
    {
      funaddr = VALUE_ADDRESS (function);
      if (TYPE_CODE (TYPE_TARGET_TYPE (ftype)) == TYPE_CODE_TYPEDEF)
	value_type = TYPE_TARGET_TYPE (TYPE_TARGET_TYPE (ftype));
      else
	value_type = TYPE_TARGET_TYPE (ftype);
    }
  else if (code == TYPE_CODE_PTR)
    {
      funaddr = value_as_address (function);
      ftype = check_typedef (TYPE_TARGET_TYPE (ftype));
      if (TYPE_CODE (ftype) == TYPE_CODE_FUNC
	  || TYPE_CODE (ftype) == TYPE_CODE_METHOD)
	{
	  funaddr = gdbarch_convert_from_func_ptr_addr (current_gdbarch,
							funaddr,
							&current_target);
	  value_type = TYPE_TARGET_TYPE (ftype);
	}
      else
	value_type = builtin_type_int;
    }
  else if (code == TYPE_CODE_INT)
    {
      /* Handle the case of functions lacking debugging info.
         Their values are characters since their addresses are char */
      if (TYPE_LENGTH (ftype) == 1)
	funaddr = value_as_address (value_addr (function));
      else
	/* Handle integer used as address of a function.  */
	funaddr = (CORE_ADDR) value_as_long (function);

      value_type = builtin_type_int;
    }
  else if (code == TYPE_CODE_ERROR)
    {
      value_type = builtin_type_error;
    }
  else
    error (_("Invalid data type for function to be called."));

  if (retval_type != NULL)
    *retval_type = value_type;
  return funaddr + DEPRECATED_FUNCTION_START_OFFSET;
}

/* Call breakpoint_auto_delete on the current contents of the bpstat
   pointed to by arg (which is really a bpstat *).  */

static void
breakpoint_auto_delete_contents (void *arg)
{
  breakpoint_auto_delete (*(bpstat *) arg);
}

static CORE_ADDR
generic_push_dummy_code (struct gdbarch *gdbarch,
			 CORE_ADDR sp, CORE_ADDR funaddr,
			 struct value **args, int nargs,
			 struct type *value_type,
			 CORE_ADDR *real_pc, CORE_ADDR *bp_addr)
{
  /* Something here to findout the size of a breakpoint and then
     allocate space for it on the stack.  */
  int bplen;
  /* This code assumes frame align.  */
  gdb_assert (gdbarch_frame_align_p (gdbarch));
  /* Force the stack's alignment.  The intent is to ensure that the SP
     is aligned to at least a breakpoint instruction's boundary.  */
  sp = gdbarch_frame_align (gdbarch, sp);
  /* Allocate space for, and then position the breakpoint on the
     stack.  */
  if (gdbarch_inner_than (gdbarch, 1, 2))
    {
      CORE_ADDR bppc = sp;
      gdbarch_breakpoint_from_pc (gdbarch, &bppc, &bplen);
      sp = gdbarch_frame_align (gdbarch, sp - bplen);
      (*bp_addr) = sp;
      /* Should the breakpoint size/location be re-computed here?  */
    }      
  else
    {
      (*bp_addr) = sp;
      gdbarch_breakpoint_from_pc (gdbarch, bp_addr, &bplen);
      sp = gdbarch_frame_align (gdbarch, sp + bplen);
    }
  /* Inferior resumes at the function entry point.  */
  (*real_pc) = funaddr;
  return sp;
}

/* For CALL_DUMMY_ON_STACK, push a breakpoint sequence that the called
   function returns to.  */

static CORE_ADDR
push_dummy_code (struct gdbarch *gdbarch,
		 CORE_ADDR sp, CORE_ADDR funaddr,
		 struct value **args, int nargs,
		 struct type *value_type,
		 CORE_ADDR *real_pc, CORE_ADDR *bp_addr)
{
  if (gdbarch_push_dummy_code_p (gdbarch))
    return gdbarch_push_dummy_code (gdbarch, sp, funaddr,
				    args, nargs, value_type, real_pc, bp_addr);
  else    
    return generic_push_dummy_code (gdbarch, sp, funaddr,
				    args, nargs, value_type, real_pc, bp_addr);
}

/* APPLE LOCAL: Added the ability to time out the hand function
   call.  */

static int timer_fired;
static int hand_call_function_timeout;

int 
set_hand_function_call_timeout (int newval)
{
  int oldvalue = hand_call_function_timeout;
  hand_call_function_timeout = newval;
  return oldvalue;
}

int
hand_function_call_timeout_p ()
{
  return timer_fired;
}

static void
handle_alarm_while_calling (int signo)
{
  timer_fired = 1;
  target_stop ();
}

/* EMBARCADERO Local: begin fCall wrapper */
/* Global structure to hold the info needed by the fCall wrapper code for
   the current function call.  */
static struct fcallwrapper_info startup_fcw;
static struct fcallwrapper_info *current_fcw = &startup_fcw;

/* Init the fCall wrapper info.  */
static void
init_fcallwrapper_info (struct fcallwrapper_info *fcw)
{
  gdb_assert (fcw);
  memset (fcw, 0, sizeof (*fcw));
}

/* Return the current function call wrapper info.  */
struct fcallwrapper_info *
get_current_fcw (void)
{
  return current_fcw;
}

/* Return 1 if the current function call wrapper is being used (i.e.
   we're in the process of calling a function through the function call
   wrapper).  */
int
using_current_fcw (void)
{
  return (current_fcw->fcallwrapper_addr != 0);
}

/* Push the current fCall wrapper info.  */
void
push_current_fcw (void)
{
  struct fcallwrapper_info *fcw = XMALLOC (struct fcallwrapper_info);
  init_fcallwrapper_info (fcw);
  fcw->next = current_fcw;
  current_fcw = fcw;
}

/* Pop the current fCall wrapper info and reset any changed state.  */
void
pop_current_fcw (void)
{
  struct fcallwrapper_info *fcw = current_fcw;
  gdb_assert (fcw);

  /* Unset temporary BPs at fCall wrapper control points.  */
  /* DAWN/KIRILL FIXME: what if nested in outer FCW call?  */
  if (fcw->ReadyToPushPoint_bpt)
    delete_breakpoint (fcw->ReadyToPushPoint_bpt);
  if (fcw->CatchPoint_bpt)
    delete_breakpoint (fcw->CatchPoint_bpt);
  if (fcw->ResultFetchPoint_bpt)
    delete_breakpoint (fcw->ResultFetchPoint_bpt);

   /* We always keep a static copy around so that it's safe to reference,
      so if this is the top of the stack, just zero it.  */
  if (fcw->next)
    {
      current_fcw = fcw->next;
      xfree (fcw);
    }
  else
    {
      fcw->ReadyToPushPoint_bpt = 0;
      fcw->CatchPoint_bpt = 0;
      fcw->ResultFetchPoint_bpt = 0;
    }
}

/* Version of pop_current_fcw that can be called by cleanup code.  */
static void
pop_current_fcw_cleanup (void *dummy)
{
  pop_current_fcw ();
}

/* Cleanup the fCall wrapper info.  */
void
cleanup_fcallwrapper_info ()
{
   /* We always keep a static copy around so that it's safe to reference,
      so if this is the top of the stack, just zero it.  */
  while (current_fcw->next)
    {
      pop_current_fcw ();
    }
}

/* Record that the function call wrapper caught an exception thrown by
   the user's function.  */
void
set_fcw_exception_raised (void)
{
  current_fcw->fCallCatchTriggered = 1;
}

/* Return 1 if the function call wrapper caught an exception which was
   thrown by the user's function.  */
int
fcw_exception_raised (void)
{
  return current_fcw->fCallCatchTriggered;
}

/* fCall Wrapper control point setter:
   Set a temporary BP at BP_ADDR with BP_NAME at frame SP.  */
static struct breakpoint *
set_fcw_breakpoint (CORE_ADDR bp_addr, const char *bp_name, CORE_ADDR sp)
{
  struct breakpoint *bpt;
  struct symtab_and_line sal;
  struct frame_id dummy_id;
  char buf[64];

  init_sal (&sal);		/* initialize to zeroes */
  sal.pc = bp_addr;
  sal.pc = gdbarch_addr_bits_remove (current_gdbarch, sal.pc);
  if (file_log)
    fprintf_unfiltered (file_log, "Setting %s BP at: %s\n",
			bp_name, paddr (sal.pc));
  sal.section = find_pc_overlay (sal.pc);
  dummy_id = frame_id_build (sp, sal.pc);
  bpt = set_momentary_breakpoint (sal, dummy_id, bp_call_dummy);
  bpt->disposition = disp_del;
  sprintf (&buf[0], bp_name);
  bpt->addr_string = savestring (&buf[0],
				 (char*)((char*)buf + strlen(buf) + 1) - &buf[0]);
  return bpt;
}

/* Helper function for fcw_breakpoint_hit().
   Find which FCW is responsible for setting this FCW BP
   and clear the BP.  Return 1 on success.  */
static int
find_fcw_breakpoint (struct fcallwrapper_info *fcw,
		     struct breakpoint *bpt, const char *bp_name)
{
  /* See which of our FCW control BPs this is.  */
  gdb_assert (fcw);
  if (fcw->fcallwrapper_addr == 0 && fcw->next)
    {
      /* This one isn't in use - try our parent.  */
      return find_fcw_breakpoint (fcw->next, bpt, bp_name);
    }
  if (bpt == fcw->ReadyToPushPoint_bpt)
    {
      gdb_assert (strcmp (bp_name, "fCallWrapperReadyToArgPush") == 0);
      fcw->ReadyToPushPoint_bpt = 0;
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall wrapper: stopped at arg push point, address: %s\n", 
			    paddr (bpt->loc->address));
      delete_breakpoint (bpt);
      return 1;
    }
  else if (bpt == fcw->CatchPoint_bpt)
    {
      gdb_assert (strcmp (bp_name, "fCallWrapperCatch") == 0);
      fcw->CatchPoint_bpt = 0;
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall wrapper: stopped at catchaddr, address: %s\n",
			    paddr (bpt->loc->address));

      delete_breakpoint (bpt);
      return 1;
    }
  else if (bpt == fcw->ResultFetchPoint_bpt)
    {
      gdb_assert (strcmp (bp_name, "fCallWrapperGetResult") == 0);
      fcw->ResultFetchPoint_bpt = 0;
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall wrapper: stopped at getresultaddr, address: %s\n",
			    paddr (bpt->loc->address));
    }
  else
    {
      if (fcw->next)
	{
	  /* Not in this FCW - try our parent.  */
	  return find_fcw_breakpoint (fcw->next, bpt, bp_name);
	}
      /* Not found :(  */
      return 0;
    }
  delete_breakpoint (bpt);
  return 1;
}

/* fCall Wrapper control point checker:
   Test if the BP is one of our FCW control BPs with BP_NAME.
   If so, delete the BP and return 1, else return 0.  */
int
fcw_breakpoint_hit (struct breakpoint *bpt, const char *bp_name)
{
  struct fcallwrapper_info *fcw = get_current_fcw ();

  /* Return 0 if the name doesn't match.  */
  if ((bpt == NULL)
      || (bpt->addr_string == NULL)
      || (strcmp (bpt->addr_string, bp_name) != 0))
    return 0;

  /* Search for this BP in our stack of FCWs.  */
  if (find_fcw_breakpoint (fcw, bpt, bp_name))
    return 1;

  /* FCW control BP not found.  This shouldn't happen.  Report an error.  */
  error ("Unknown breakpoint \"%s\" hit during function call wrapper invokation\"", bp_name);

  return 0;
}

/* EMBARCADERO Local: WORKAROUND against N_SECT Thumb bit bug: 
   Use g_examine_i_size variable to force Thumb disasm mode 
   for __dbk_fcall_wrapper Delphi RTL function */
#if defined (TARGET_ARM)
extern char g_examine_i_size;
#endif
/* EMBARCADERO Local: End */

/* Check if the RTL will permit us to call functions:

   For Pascal, search for the fCall wrapper function symbol "dbkFCallWrapperAddr"
   in the user's code.

    Return 1 on success, else 0.  */

static int
fcw_can_call_function ()
{
  CORE_ADDR fcallwrapper_addr = 0;
  struct minimal_symbol *fcallwrapper_sym = NULL;

  /* For Pascal, we check for "dbkFCallWrapperAddr" in addition to "__dbk_fcall_wrapper".
     FIXME: why do we do this?  Kirill added this, so we'll continue to check.
     Search for the fCall wrapper address symbol "dbkFCallWrapperAddr" and
     dereference it as int* - we should check if RTL initialized, Delphi specific only. */
  if (current_language->la_language == language_pascal)
    {
      CORE_ADDR addr = 0;
      struct minimal_symbol *addr_sym = NULL;
      int errcode;

      addr_sym = lookup_minimal_symbol ("dbkFCallWrapperAddr", NULL, NULL);
      if (!addr_sym)
	{
	  if (file_log)
	    fprintf_unfiltered (file_log, "Unable to locate dbkFCallWrapperAddr symbol in target.\n");
          return 0;
	}
      addr = SYMBOL_VALUE_ADDRESS (addr_sym);
      if (addr != 0) 
	{
	  CORE_ADDR ptrvalue;
	  errcode = target_read_memory (addr, (char*)&ptrvalue, sizeof(addr));
	  if (!ptrvalue)
	    {
	      if (file_log)
		fprintf_unfiltered (file_log, "dbkFCallWrapperAddr has not been set yet, function call aborted.\n");
	      return 0;
	    }
	}
      else
	{
	  if (file_log)
	    fprintf_unfiltered (file_log, "Unable to dereference dbkFCallWrapperAddr ptr in target.\n");
          return 0;
	}
      if (file_log)
	fprintf_unfiltered (file_log, "dbkFCallWrapperAddr check passed, proceed with function call.\n");
    }

  return 1;
}

/* Check if we can use the Delphi RTL's function call wrapper:

   Search for the RTL's initialization flag symbol "dbk_RTL_initialized" and
   fail if not found or not set to 1.

   Search for the fCall wrapper function symbol "__dbk_fcall_wrapper"
   in the user's code and return the address if found.

    On success, return:
	*FCALLWRAPPER_ADDR_P = address of "__dbk_fcall_wrapper"
    Return 1 on success, else 0.  */

static int
fcw_can_use_fcallwrapper (CORE_ADDR *fcallwrapper_addr_p)
{
  CORE_ADDR RTLinitialized_addr = 0;
  CORE_ADDR fcallwrapper_addr = 0;
  struct minimal_symbol *RTLinitialized_sym = NULL;
  struct minimal_symbol *fcallwrapper_sym = NULL;
  int32_t RTLinitialized_flag = 0;

  /* Init output to 0.  */
  *fcallwrapper_addr_p = 0;

// FIXME: the check for dbk_RTL_initialized isn't working correctly on C++ for some reason.
// Until we can figure out why, we'll only perform the check in Delphi.
#define DISABLE_RTL_INIT_CHECK_ON_CPP
#ifdef DISABLE_RTL_INIT_CHECK_ON_CPP
  if (current_language->la_language == language_pascal)
  {
#endif
  /* Search for the RTL initialized flag symbol "dbk_RTL_initialized".
     If the RTL is ready, it will set dbk_RTL_initialized to 1.
     If the Delphi RTL isn't initialized yet, don't try and use its fCall wrapper.
     Instead, use gdb's internal function call support for unwinding from exceptions.  */
  RTLinitialized_sym
    = lookup_minimal_symbol ("dbk_RTL_initialized", NULL, NULL);
  if (!RTLinitialized_sym)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate dbk_RTL_initialized symbol in target.\n");
      return 0;
    }
  RTLinitialized_addr = SYMBOL_VALUE_ADDRESS (RTLinitialized_sym);
  if (!RTLinitialized_addr)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate address of dbk_RTL_initialized symbol in target.\n");
      return 0;
    }
  if (file_log)
    fprintf_unfiltered (file_log,
			"dbk_RTL_initialized symbol found at %s\n",
			paddr (RTLinitialized_addr));
  /* Read the value of the RTL's initialized flag at dbk_RTL_initialized.  */
  {
    int errcode = EIO;			/* Error from last read. */
    errcode = target_read_memory (RTLinitialized_addr, (gdb_byte*)&RTLinitialized_flag, 4);
    if (errcode != 0)
      {
	if (file_log)
	  fprintf_unfiltered (file_log, "Read of dbk_RTL_initialized symbol failed, errcode = %d.\n", errcode);
	return 0;
      }
    }
  if (!RTLinitialized_flag)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "RTL is not yet initalized.\n");
      return 0;
    }
#ifdef DISABLE_RTL_INIT_CHECK_ON_CPP
  }
#endif

  /* Search for the fCall wrapper function symbol "__dbk_fcall_wrapper".  */
  fcallwrapper_sym
    = lookup_minimal_symbol ("__dbk_fcall_wrapper", NULL, NULL);
  if (!fcallwrapper_sym)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate __dbk_fcall_wrapper symbol in target.\n");
      return 0;
    }
  fcallwrapper_addr = SYMBOL_VALUE_ADDRESS (fcallwrapper_sym);
  if (!fcallwrapper_addr)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate address of __dbk_fcall_wrapper symbol in target.\n");
      return 0;
    }
  if (file_log)
    fprintf_unfiltered (file_log,
			"__dbk_fcall_wrapper function found at %s\n",
			paddr (fcallwrapper_addr));

  /* Return the adress. */
  *fcallwrapper_addr_p = fcallwrapper_addr;
  return 1;
}

/* fCall Wrapper symbol lookup and control points scanner:
  
   Figure out if we can use the function call wrapper and if so,
   prepare the CURRENT_FCW and set the FCW control BPs.

   SP is the user's stack address.
   REAL_PC_P is a pointer to the user's PC.  Report an error if 
   the low bit of *REAL_PC_P is set.
   KIRILL FIXME: Move ARM Thumb bit specific to ARM dep module.

   Search for the fCall wrapper function symbol "__dbk_fcall_wrapper"
   in the user's code and set:
	fcw->fcallwrapper_addr = addr of "__dbk_fcall_wrapper"
	fcw->user_real_pc      = real_pc
   Then scan the function for key control points by dissassembling
   the code in the first 0x130 bytes at fcallwrapper_addr and looking for
   instructions "bl Sysinit.__dbkFCallArgs".
   Then set the temporary FCW control BPs:
	fcw->ReadyToPushPoint_bpt = BP at addr of 1st call to __dbkFCallArgs
	fcw->user_lr              = addr of next instruction after 1st call
	fcw->ResultFetchPoint_bpt = BP at addr of next instruction
	fcw->CatchPoint_bpt       = BP at addr of 2nd call to __dbkFCallArgs

    On success, return:
	*FCALLWRAPPER_VAL_P = value of "__dbk_fcall_wrapper"
	*REAL_PC_P          = reset to (addr of "__dbk_fcall_wrapper" | 1)
    Return 1 on success, else 0.  */

static int
fcw_scan_fcallwrapper (CORE_ADDR *real_pc_p,
		       CORE_ADDR sp,
		       struct value **fcallwrapper_val_p)
{
  struct fcallwrapper_info *fcw = get_current_fcw ();
  CORE_ADDR fcallwrapper_addr = 0;
  CORE_ADDR fcw_ReadyToPushPoint = 0;
  CORE_ADDR fcw_ResultFetchPoint = 0;
  CORE_ADDR fcw_CatchPoint = 0;
  CORE_ADDR fcallwrapper_low, fcallwrapper_high;
  CORE_ADDR real_pc = *real_pc_p;
  struct minimal_symbol *fcallwrapper_sym = NULL;
  struct value *fcallwrapper_val = NULL;

/* EMBARCADERO Local: WORKAROUND against N_SECT Thumb bit bug:
   force Thumb disasm mode here */
#if defined (TARGET_ARM)
  g_examine_i_size = 'h';
#endif

  /* Init output to 0.  */
  *fcallwrapper_val_p = NULL;

  if (!fcw_can_use_fcallwrapper (&fcallwrapper_addr))
    return 0;

  fcallwrapper_val = find_function_in_inferior ("__dbk_fcall_wrapper", NULL);
  if (!fcallwrapper_val)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to determine value of __dbk_fcall_wrapper.\n");
      return 0;
    }

  /* Find reliable fCall wrapper function range.  */
  fcallwrapper_low = fcallwrapper_addr;
  /* Set high scan window boundary.
     We can't use exact wrapper AT_high value because we have exported sym (AT_low) only.*/
  fcallwrapper_high = fcallwrapper_low + 0x2F0;

  while (fcallwrapper_low < fcallwrapper_high)
    {
      struct ui_file *disasm_mem_dump;
      char* disasm_text; 
      long disasm_text_length;
      int insn_length = 0;

      if (file_log)
	fprintf_unfiltered (file_log, "%s:\t",
			    paddr (fcallwrapper_low));
      disasm_mem_dump = mem_fileopen ();
      insn_length = gdb_print_insn (fcallwrapper_low, disasm_mem_dump);
      disasm_text = ui_file_xstrdup (disasm_mem_dump, &disasm_text_length);

      /* Check for fCall wrapper __dbkFCallArgs calls.  */
      if ((strstr (disasm_text, "Sysinit.__dbkFCallArgs") != NULL)
	  && !fcw_ReadyToPushPoint)
	{
	  /* First call to __dbkFCallArgs found.  */
	  if (file_log)
	    fprintf_unfiltered (file_log, "%s:\t%s\n", "ReadyToPushPoint",
				disasm_text);
	  fcw_ReadyToPushPoint = fcallwrapper_low;
	  fcw_ResultFetchPoint = fcallwrapper_low + insn_length;
	}
      else if ((strstr (disasm_text, "Sysinit.__dbkFCallArgs") != NULL)
	       && fcw_ReadyToPushPoint)
	{        
	  /* Second call to __dbkFCallArgs found.  */
	  if (file_log)
	    fprintf_unfiltered (file_log, "%s:\t%s\n", "CatchPoint",
				disasm_text);
	  fcw_CatchPoint = fcallwrapper_low;
	} 
      else
	if (file_log)
	  fprintf_unfiltered (file_log, "%s\n", disasm_text);

      fcallwrapper_low = fcallwrapper_low + insn_length;
      ui_file_delete (disasm_mem_dump);
    }

#if 0 /* DELETEME: May be needed in future in case debuggee address space
	 injection is chosen.  */
  /* Disable host debug images read here - get pure .text contents from
     target.  */
  if (file_log)
    {
      set_trust_readonly (0);
      while (fcallwrapper_low < fcallwrapper_high)
	{
	  fprintf_unfiltered (file_log, "%s:\t",
			      paddr (fcallwrapper_low));
	  fcallwrapper_low = fcallwrapper_low
			      + gdb_print_insn (fcallwrapper_low,
						file_log);
	  fprintf_unfiltered (file_log, "\n");
	}
      set_trust_readonly (1);
    }
#endif /* 0 */

  /* Make sure we found all our control points.  */
  if (!fcw_ReadyToPushPoint || !fcw_CatchPoint)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate call instructions in function call wrapper.\n");
      return 0;
    }

  /* Set a few values in the current_fcw.  */
  fcw->fcallwrapper_addr = fcallwrapper_addr;
  /* The user's return addr is where we will fetch results.  */
  fcw->user_lr = fcw_ResultFetchPoint;
#if 0
  /* DELETEME: This code broke virtual function evaluation on iOS sinces we use 
     -triple thumbv7-apple-ios for iOS32 which uses APCS ABI, which uses 
     least significant bit to discriminate between non-virtual function ptrs 
     (if 0) and virtual function ptrs (if 1). The code was added to workaround
     an issue which can no longer be reproduced because of changes how struct
     returns are handled, so is safe to remove. */
  /* FIXME: Check if function address resolved via syms is not suitable for
     safe fCall. Used as workaround against problem with Self/This ptr
     parameter not parsed or passed by caller - eval.c module */
  if (real_pc & 0x1)
    error (_("function address is invalid, function call aborted"));
#endif
  fcw->user_real_pc = real_pc;
  /*  KIRILL FIXME: Move ARM Thumb bit specific to ARM dep module. */
  real_pc = fcw->fcallwrapper_addr | 1;

  /* Set temporary BPs at fCall wrapper control points:
     * fcw_ReadyToPushPoint - fCall wrapper arguments push point
     * fcw_CatchPoint - fCall Wrapper catch point
     * fcw_ResultFetchPoint - fCall Wrapper get result point
     We'll recognize these by name when we hit them.  */
  /* DAWN/KIRILL FIXME: do we need to remove these on cleanup if not
     nested in outer FCW call?  */
      
  fcw->ReadyToPushPoint_bpt
    = set_fcw_breakpoint (fcw_ReadyToPushPoint,
			  "fCallWrapperReadyToArgPush", sp);
  fcw->CatchPoint_bpt
    = set_fcw_breakpoint (fcw_CatchPoint,
			  "fCallWrapperCatch", sp);
  fcw->ResultFetchPoint_bpt
    = set_fcw_breakpoint (fcw_ResultFetchPoint,
			  "fCallWrapperGetResult", sp);

  *real_pc_p = real_pc;
  *fcallwrapper_val_p = fcallwrapper_val;
  return 1;
}
/* EMBARCADERO Local: end fCall wrapper */

/* All this stuff with a dummy frame may seem unnecessarily complicated
   (why not just save registers in GDB?).  The purpose of pushing a dummy
   frame which looks just like a real frame is so that if you call a
   function and then hit a breakpoint (get a signal, etc), "backtrace"
   will look right.  Whether the backtrace needs to actually show the
   stack at the time the inferior function was called is debatable, but
   it certainly needs to not display garbage.  So if you are contemplating
   making dummy frames be different from normal frames, consider that.  */

/* Perform a function call in the inferior.
   ARGS is a vector of values of arguments (NARGS of them).
   FUNCTION is a value, the function to be called.
   Returns a value representing what the function returned.
   May fail to return, if a breakpoint or signal is hit
   during the execution of the function.

   ARGS is modified to contain coerced values. */


struct value *
/* APPLE LOCAL hand function call */
hand_function_call (struct value *function, struct type *expect_type,
                    int nargs, struct value **args, int restore_frame)
{
  CORE_ADDR sp;
  CORE_ADDR dummy_addr;
  struct type *orig_return_type = NULL;
  struct type *values_type, *target_values_type;
  unsigned char struct_return = 0, lang_struct_return = 0;
  CORE_ADDR struct_addr = 0;
  struct regcache *retbuf;
  struct cleanup *retbuf_cleanup;
  struct cleanup *runtime_cleanup;
  struct inferior_status *inf_status;
  struct cleanup *inf_status_cleanup;
  CORE_ADDR funaddr;
  CORE_ADDR real_pc;
  struct type *ftype = check_typedef (value_type (function));
  CORE_ADDR bp_addr;
  struct regcache *caller_regcache;
  struct cleanup *caller_regcache_cleanup;
  struct frame_id dummy_id;
  struct cleanup *args_cleanup;
  int runtime_check_level;
  /* EMBARCADERO Local: fCall Wrapper */
  struct fcallwrapper_info *fcw;
  struct value *fcw_fcallwrapper_val = NULL;
  CORE_ADDR fcallwrapper_addr = 0;
  struct breakpoint *overloaded_dummy_bpt = NULL;

/* EMBARCADERO Local: WORKAROUND against N_SECT Thumb bit bug:
   Save previous g_examine_i_size global disasm variable */
#if defined (TARGET_ARM)
  char save_g_examine_i_size;
#endif

  if (!target_has_execution)
    noprocess ();

  /* EMBARCADERO LOCAL begin: fCall Wrapper */
  /* See if the RTL will permit us to call functions.  */
  if (!fcw_can_call_function ())
  {
    error (_("Unable to perform protected function calls, function call aborted."));
  }
  /* EMBARCADERO LOCAL end: fCall Wrapper */

  /* APPLE LOCAL begin */
  /* Make sure we have a viable return type for the function being called. */

  funaddr = find_function_addr (function, &orig_return_type);
  values_type = check_typedef (orig_return_type);

  /* We don't require expect_type not to be a typedef, so remember to
     run check_typedef here */

  if ((values_type == NULL) || (TYPE_CODE (values_type) == TYPE_CODE_ERROR))
    if (expect_type != NULL)
      {
	orig_return_type = expect_type;
	values_type = check_typedef (expect_type);
      }

  if ((values_type == NULL) || (TYPE_CODE (values_type) == TYPE_CODE_ERROR))
    {
      char *sym_name;
      find_pc_partial_function (funaddr, &sym_name, NULL, NULL);

      error ("Unable to call function \"%s\" at 0x%s: "
	     "no return type information available.\n"
	     "To call this function anyway, you can cast the "
	     "return type explicitly (e.g. 'print (float) fabs (3.0)')",
	     sym_name ? sym_name : "<unknown>",
	     paddr_nz (funaddr));
    }
  /* APPLE LOCAL end */

  if (!gdbarch_push_dummy_call_p (current_gdbarch))
    error (_("This target does not support function calls"));

  /* EMBARCADERO Local begin calling conventions */
  /* See if this function calling convention is supported.  
     FIXME: this should really be in the target vector.  */
  if (!gdbarch_calling_convention_supported (current_gdbarch, function))
    {
      char *sym_name;
      const char *ccstr;
      funaddr = find_function_addr (function, &values_type);
      find_pc_partial_function (funaddr, &sym_name, NULL, NULL);
      ccstr = gdbarch_calling_convention_string (current_gdbarch, function);

      error ("Unable to call function \"%s\" at 0x%s: "
	     "calling convention \"%s\" not supported",
	     sym_name ? sym_name : "<unknown>",
	     paddr_nz (funaddr),
	     ccstr ? ccstr : "<unknown>");
    }
  /* EMBARCADERO Local end calling conventions */

  /* Create a cleanup chain that contains the retbuf (buffer
     containing the register values).  This chain is created BEFORE the
     inf_status chain so that the inferior status can be cleaned up
     (restored or discarded) without having the retbuf freed.  */
  retbuf = regcache_xmalloc (current_gdbarch);
  retbuf_cleanup = make_cleanup_regcache_xfree (retbuf);

  /* APPLE LOCAL: Calling into the ObjC runtime can block against other threads
     that hold the runtime lock.  Since any random function call might go into 
     the runtime, we added a gdb mode where hand_function_call ALWAYS checks
     whether the runtime is going to be a problem.  */

  runtime_check_level = objc_runtime_check_enabled_p ();
  if (runtime_check_level)
    {
      enum objc_debugger_mode_result retval;
      retval = make_cleanup_set_restore_debugger_mode (&runtime_cleanup, 
                                                       runtime_check_level);
      if (retval == objc_debugger_mode_fail_objc_api_unavailable)
        if (target_check_safe_call (OBJC_SUBSYSTEM, CHECK_SCHEDULER_VALUE))
          retval = objc_debugger_mode_success;

      if (retval != objc_debugger_mode_success)
	{
          if  (retval == objc_debugger_mode_fail_spinlock_held
               || retval == objc_debugger_mode_fail_malloc_lock_held)
            if (ui_out_is_mi_like_p (uiout))
              error ("");
            else
              error ("Canceling call as the malloc lock is held so it isn't safe to call the runtime.\n"
                     "Issue the command:\n"
                     "    set objc-non-blocking-mode off \n"
                     "to override this check if you are sure your call doesn't use the malloc libraries or the ObjC runtime.");
          
          else
            if (ui_out_is_mi_like_p (uiout))
              error ("");
            else
              error ("Canceling call as the ObjC runtime would deadlock.\n"
                     "Issue the command:\n"
                     "    set objc-non-blocking-mode off \n"
                     "to override this check if you are sure your call doesn't use the ObjC runtime.");
        }
    }
  else
    runtime_cleanup = make_cleanup (null_cleanup, 0);

  /* APPLE LOCAL: Always arrange to stop on ObjC exceptions thrown while in 
     a hand-called function: */
  if (objc_exceptions_interrupt_hand_call)
    make_cleanup_init_objc_exception_catcher ();

  /* APPLE LOCAL begin inferior function call */
#if defined (NM_NEXTSTEP)
  macosx_setup_registers_before_hand_call ();

#endif
  /* FIXME: This really needs to go in the target vector....  */
  if (inferior_function_calls_disabled_p)
    error ("Function calls from gdb are not supported on this target.");

  /* APPLE LOCAL end inferior function call */

  /* EMBARCADERO Local: fCall Wrapper init */
  /* See if we can use the Delphi RTL's fCall wrapper.  If we can,
     fcallwrapper_addr will be set to the address.  */
  if (!fcw_can_use_fcallwrapper (&fcallwrapper_addr))
    {
      /* Print a warning and proceed with normal function call
         evaluation.  */
      warning (_("The function call will be executed without the RTL's exception wrapper."));
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall will be executed without exception wrapper.\n");
    }
  /* DAWN/KIRILL FIXME: in case of nested fcall, should we skip setting
     up FCW?  What should happen if inner nested fcall not using FCW
     raises exception?  */
  /* Start a new context for the function call wrapper info and register
     it's cleanup.  Note: this must preceed the caller_regcache_cleanup
     because those cleanups are discarded below.  */
  push_current_fcw ();
  make_cleanup (pop_current_fcw_cleanup, NULL);
  fcw = get_current_fcw ();
  gdb_assert (fcw);

  /* A cleanup for the inferior status.  Create this AFTER the retbuf
     so that this can be discarded or applied without interfering with
     the regbuf.  */
  inf_status = save_inferior_status (1);
  inf_status_cleanup = make_cleanup_restore_inferior_status (inf_status);

  /* Save the caller's registers so that they can be restored once the
     callee returns.  To allow nested calls the registers are (further
     down) pushed onto a dummy frame stack.  Include a cleanup (which
     is tossed once the regcache has been pushed).  */
  caller_regcache = frame_save_as_regcache (get_current_frame ());
  caller_regcache_cleanup = make_cleanup_regcache_xfree (caller_regcache);

  /* Ensure that the initial SP is correctly aligned.  */
  {
    CORE_ADDR old_sp = read_sp ();
    if (gdbarch_frame_align_p (current_gdbarch))
      {
	sp = gdbarch_frame_align (current_gdbarch, old_sp);
	/* NOTE: cagney/2003-08-13: Skip the "red zone".  For some
	   ABIs, a function can use memory beyond the inner most stack
	   address.  AMD64 called that region the "red zone".  Skip at
	   least the "red zone" size before allocating any space on
	   the stack.  */
	if (INNER_THAN (1, 2))
	  sp -= gdbarch_frame_red_zone_size (current_gdbarch);
	else
	  sp += gdbarch_frame_red_zone_size (current_gdbarch);
	/* Still aligned?  */
	gdb_assert (sp == gdbarch_frame_align (current_gdbarch, sp));
	/* NOTE: cagney/2002-09-18:
	   
	   On a RISC architecture, a void parameterless generic dummy
	   frame (i.e., no parameters, no result) typically does not
	   need to push anything the stack and hence can leave SP and
	   FP.  Similarly, a frameless (possibly leaf) function does
	   not push anything on the stack and, hence, that too can
	   leave FP and SP unchanged.  As a consequence, a sequence of
	   void parameterless generic dummy frame calls to frameless
	   functions will create a sequence of effectively identical
	   frames (SP, FP and TOS and PC the same).  This, not
	   suprisingly, results in what appears to be a stack in an
	   infinite loop --- when GDB tries to find a generic dummy
	   frame on the internal dummy frame stack, it will always
	   find the first one.

	   To avoid this problem, the code below always grows the
	   stack.  That way, two dummy frames can never be identical.
	   It does burn a few bytes of stack but that is a small price
	   to pay :-).  */
	if (sp == old_sp)
	  {
	    if (INNER_THAN (1, 2))
	      /* Stack grows down.  */
	      sp = gdbarch_frame_align (current_gdbarch, old_sp - 1);
	    else
	      /* Stack grows up.  */
	      sp = gdbarch_frame_align (current_gdbarch, old_sp + 1);
	  }
	gdb_assert ((INNER_THAN (1, 2) && sp <= old_sp)
		    || (INNER_THAN (2, 1) && sp >= old_sp));
      }
    else
      /* FIXME: cagney/2002-09-18: Hey, you loose!

	 Who knows how badly aligned the SP is!

	 If the generic dummy frame ends up empty (because nothing is
	 pushed) GDB won't be able to correctly perform back traces.
	 If a target is having trouble with backtraces, first thing to
	 do is add FRAME_ALIGN() to the architecture vector. If that
	 fails, try unwind_dummy_id().

         If the ABI specifies a "Red Zone" (see the doco) the code
         below will quietly trash it.  */
      sp = old_sp;
  }

  /* APPLE LOCAL move typedef check up */
  /* The funaddr and typedef checks are moved up for some reason.  */

  /* Are we returning a value using a structure return (passing a
     hidden argument pointing to storage) or a normal value return?
     There are two cases: language-mandated structure return and
     target ABI structure return.  The variable STRUCT_RETURN only
     describes the latter.  The language version is handled by passing
     the return location as the first parameter to the function,
     even preceding "this".  This is different from the target
     ABI version, which is target-specific; for instance, on ia64
     the first argument is passed in out0 but the hidden structure
     return pointer would normally be passed in r8.  */

  /* Ask arch, then language if function result type is supported */
  if (using_struct_return (value_type (function), values_type))
    {    
	if (language_pass_by_reference (values_type))
	{
	  lang_struct_return = 1;
	  struct_return = 1;
	  target_values_type = values_type;
	}
	else
	  error ("Passing of result pointer not supported for function result type.");
    }
  else
    target_values_type = values_type;

  /* Determine the location of the breakpoint (and possibly other
     stuff) that the called function will return to.  The SPARC, for a
     function returning a structure or union, needs to make space for
     not just the breakpoint but also an extra word containing the
     size (?) of the structure being passed.  */

  /* The actual breakpoint (at BP_ADDR) is inserted separatly so there
     is no need to write that out.  */

  switch (CALL_DUMMY_LOCATION)
    {
    case ON_STACK:
      /* "dummy_addr" is here just to keep old targets happy.  New
	 targets return that same information via "sp" and "bp_addr".  */
      if (INNER_THAN (1, 2))
	{
	  sp = push_dummy_code (current_gdbarch, sp, funaddr,
				args, nargs, target_values_type,
				&real_pc, &bp_addr);
	  dummy_addr = sp;
	}
      else
	{
	  dummy_addr = sp;
	  sp = push_dummy_code (current_gdbarch, sp, funaddr,
				args, nargs, values_type,
				&real_pc, &bp_addr);
	}
      break;
    case AT_ENTRY_POINT:
      real_pc = funaddr;
      /* EMBARCADERO Local: Use RTL known fCall return points 
         instead of app global entry point.  */
      {
	CORE_ADDR dbghook_addr = 0;
	struct breakpoint *dup_line_file_bpt = NULL;
	struct minimal_symbol *m;
	struct minimal_symbol *m1;
	struct minimal_symbol *m2;

	/* FMX app.  */
	m1 = lookup_minimal_symbol_text ("_FMXstart", NULL);
	/* Console app.  */
	m2 = lookup_minimal_symbol_text ("main", NULL);

	if (m1 != NULL)
	  m = m1;
	else if (m2 != NULL)
	  m = m2;
	else
	  m = NULL;   

	if (m != NULL)
	  {
	    dbghook_addr = SYMBOL_VALUE_ADDRESS (m);
	    if (file_log)
	      fprintf_unfiltered (file_log, "fCall dummy ret point at %s\n",
				  paddr (dbghook_addr));
	    if (dbghook_addr != 0)
		dummy_addr = dbghook_addr;
	    else
	      dummy_addr = entry_point_address ();
	  }
	else
	  dummy_addr = entry_point_address ();
      }
      /* Make certain that the address points at real code, and not a
         function descriptor.  */
      dummy_addr = gdbarch_convert_from_func_ptr_addr (current_gdbarch,
						       dummy_addr,
						       &current_target);

      /* Let's check if current PC at chosen dummy_addr and move dummy_addr past 
         main func prologue, if so. */	
      if (dummy_addr == read_pc())
	  dummy_addr = SKIP_PROLOGUE (dummy_addr);

      /* A call dummy always consists of just a single breakpoint, so
         it's address is the same as the address of the dummy.  */
      bp_addr = dummy_addr;
      break;
    case AT_SYMBOL:
      /* Some executables define a symbol __CALL_DUMMY_ADDRESS whose
	 address is the location where the breakpoint should be
	 placed.  Once all targets are using the overhauled frame code
	 this can be deleted - ON_STACK is a better option.  */
      {
	struct minimal_symbol *sym;

	sym = lookup_minimal_symbol ("__CALL_DUMMY_ADDRESS", NULL, NULL);
	real_pc = funaddr;
	if (sym)
	  dummy_addr = SYMBOL_VALUE_ADDRESS (sym);
	else
	  dummy_addr = entry_point_address ();
	/* Make certain that the address points at real code, and not
	   a function descriptor.  */
	dummy_addr = gdbarch_convert_from_func_ptr_addr (current_gdbarch,
							 dummy_addr,
							 &current_target);
	/* A call dummy always consists of just a single breakpoint,
	   so it's address is the same as the address of the dummy.  */
	bp_addr = dummy_addr;
	break;
      }
    default:
      internal_error (__FILE__, __LINE__, _("bad switch"));
    }

  if (nargs < TYPE_NFIELDS (ftype))
    error (_("too few arguments in function call"));

  {
    int i;
    for (i = nargs - 1; i >= 0; i--)
      {
	int prototyped;
	struct type *param_type;
	
	/* FIXME drow/2002-05-31: Should just always mark methods as
	   prototyped.  Can we respect TYPE_VARARGS?  Probably not.  */
	/* APPLE LOCAL: If we don't have debug information for the
	   function being called, assume that it IS prototyped.  That
	   way if the person who has called it set the argument types 
	   correctly, we won't override them (like coercing floats to 
	   doubles.  */
	if (ftype_has_debug_info_p (ftype) == 0)
	  prototyped = 1;
	else if (TYPE_CODE (ftype) == TYPE_CODE_METHOD)
	  prototyped = 1;
	else if (i < TYPE_NFIELDS (ftype))
	  prototyped = TYPE_PROTOTYPED (ftype);
	else
	  prototyped = 0;

	if (i < TYPE_NFIELDS (ftype))
	  param_type = TYPE_FIELD_TYPE (ftype, i);
	else
	  param_type = NULL;

	/* EMBARCADERO LOCAL: begin Delphi ABI */
	/* Are we passing a value using a structure reference or a normal
	   value?  */
	if (param_type && using_pass_value_as_reference (function, param_type))
	  {
	    /* KIRILL FIXME: Add actual argument value allocation in debuggee
	       memory in cases function expect formal argument as reference but
	       actual argument is value - constant, for example.
	       DAWN FIXME: check for types those must be passed as reference
	       should be performed in corresponding language module.  */
	    if ((param_type == NULL)
	        || (!language_pass_by_reference (param_type)))
	      error ("Passing of argument via reference not supported for argument type.");
	    else if (param_type 
	             && language_pass_by_reference (param_type)
	             && (VALUE_LVAL (args[i]) == lval_memory))
	                args[i] = value_addr (args[i]);
	  }
	else if (param_type 
	         && (TYPE_CODE (param_type) == TYPE_CODE_REF)
	         && (VALUE_LVAL (args[i]) != lval_memory))
	  {
	    CORE_ADDR addr;
	    int len;		/*  = TYPE_LENGTH (arg_type); */
	    int aligned_len;
	    struct type *arg_type = check_typedef (value_enclosing_type (args[i]));

	    len = TYPE_LENGTH (arg_type);

	    aligned_len = len;
	    if (INNER_THAN (1, 2))
	      {
		/* stack grows downward */
		sp -= aligned_len;
		/* ... so the address of the thing we push is the
		   stack pointer after we push it.  */
		addr = sp;
	      }
	    else
	      {
		/* The stack grows up, so the address of the thing
		   we push is the stack pointer before we push it.  */
		addr = sp;
		sp += aligned_len;
	      }
	    /* Push the structure.  */
	    write_memory (addr, value_contents_all (args[i]), len);
	    /* The value we're going to pass is the address of the
	       thing we just pushed.  */
	    args[i] = value_from_pointer (lookup_pointer_type (arg_type),
					  addr);
	  }
	else if (param_type 
	         && (TYPE_CODE (param_type) == TYPE_CODE_STRING)
	         && (VALUE_LVAL (args[i]) == lval_memory))
	  {
	    struct type *arg_type = check_typedef (value_type (args[i]));

	    /* Function formal parameter type does not have associated pointer or/and 
           reference type - this means parameter must be passed by value exactly.
           The value we're going to pass is the dereferenced pointer to pointer 
           which representing Delphi string passed by "value". 
           For Delphi functions and Delphi string type only. */
	    if ((!param_type->pointer_type) 
		     && (!param_type->reference_type)
		     && (TYPE_CODE (arg_type) == TYPE_CODE_STRING)
	         && (TYPE_DELPHI_ABI (ftype))
	         && (current_language->la_language == language_pascal)) 
	       args[i] = value_at (arg_type, VALUE_ADDRESS(args[i]));
	    else
	  	   args[i] = value_arg_coerce (args[i], param_type, prototyped);
	  }
	else
	  args[i] = value_arg_coerce (args[i], param_type, prototyped);

	/* EMBARCADERO LOCAL: end Delphi ABI */
      }
  }

  if (gdbarch_deprecated_reg_struct_has_addr_p (current_gdbarch))
    {
      int i;
      /* This is a machine like the sparc, where we may need to pass a
	 pointer to the structure, not the structure itself.  */
      for (i = nargs - 1; i >= 0; i--)
	{
	  struct type *arg_type = check_typedef (value_type (args[i]));
	  if ((TYPE_CODE (arg_type) == TYPE_CODE_STRUCT
	       || TYPE_CODE (arg_type) == TYPE_CODE_UNION
	       || TYPE_CODE (arg_type) == TYPE_CODE_ARRAY
	       || TYPE_CODE (arg_type) == TYPE_CODE_STRING
	       || TYPE_CODE (arg_type) == TYPE_CODE_BITSTRING
	       || TYPE_CODE (arg_type) == TYPE_CODE_SET
	       || (TYPE_CODE (arg_type) == TYPE_CODE_FLT
		   && TYPE_LENGTH (arg_type) > 8)
	       )
	      && gdbarch_deprecated_reg_struct_has_addr
		   (current_gdbarch, /* using_gcc */ 0, arg_type))
	    {
	      CORE_ADDR addr;
	      int len;		/*  = TYPE_LENGTH (arg_type); */
	      int aligned_len;
	      arg_type = check_typedef (value_enclosing_type (args[i]));
	      len = TYPE_LENGTH (arg_type);

	      aligned_len = len;
	      if (INNER_THAN (1, 2))
		{
		  /* stack grows downward */
		  sp -= aligned_len;
		  /* ... so the address of the thing we push is the
		     stack pointer after we push it.  */
		  addr = sp;
		}
	      else
		{
		  /* The stack grows up, so the address of the thing
		     we push is the stack pointer before we push it.  */
		  addr = sp;
		  sp += aligned_len;
		}
	      /* Push the structure.  */
	      write_memory (addr, value_contents_all (args[i]), len);
	      /* The value we're going to pass is the address of the
		 thing we just pushed.  */
	      args[i] = value_from_pointer (lookup_pointer_type (arg_type),
					    addr);
	    }
	}
    }


  /* Reserve space for the return structure to be written on the
     stack, if necessary.  Make certain that the value is correctly
     aligned. */

  if (struct_return || lang_struct_return)
    {
      int len;

      if (values_type->pointer_type)
        len = TYPE_LENGTH (values_type->pointer_type);
      else if (values_type->reference_type)
        len = TYPE_LENGTH (values_type->reference_type);
      else if (TYPE_CODE(values_type) == TYPE_CODE_PTR
		&& TYPE_TARGET_TYPE (values_type) != NULL
		&& TYPE_DELPHI_CLASS (TYPE_TARGET_TYPE (values_type)))
        len = TYPE_LENGTH (TYPE_TARGET_TYPE (values_type));
      else
        error ("Passing of result pointer not supported for function result type.");

      /* EMBARCADERO Local: result may be returned by value or pointer 
         at struct_addr. For making sure we should calculate max possible 
         result length to fit result */
      if(len < TYPE_LENGTH (values_type))
        len = TYPE_LENGTH (values_type);

      if (INNER_THAN (1, 2))
	{
	  /* Stack grows downward.  Align STRUCT_ADDR and SP after
             making space for the return value.  */
	  /* EMBARCADERO Local: Result buffer must be zeroed to eliminate
	     problems with RTL string cleanup functions */
	  char *zerochars = xmalloc (len);
	  memset (zerochars, 0, len);
	  sp -= len;
	  if (gdbarch_frame_align_p (current_gdbarch))
	    sp = gdbarch_frame_align (current_gdbarch, sp);
	  struct_addr = sp;
	  write_memory (struct_addr, (const gdb_byte *)zerochars, len);
	  xfree (zerochars);
	}
      else
	{
	  /* Stack grows upward.  Align the frame, allocate space, and
             then again, re-align the frame??? */
	  if (gdbarch_frame_align_p (current_gdbarch))
	    sp = gdbarch_frame_align (current_gdbarch, sp);
	  struct_addr = sp;
	  sp += len;
	  if (gdbarch_frame_align_p (current_gdbarch))
	    sp = gdbarch_frame_align (current_gdbarch, sp);
	}
    }

    args_cleanup = make_cleanup (null_cleanup, NULL);

// EMBARCADERO DELETEME - temporary hack to allow old fcall to continue to work
#define IF_USE_FCALL_WRAPPER if (getenv ("DONT_USE_FCALL_WRAPPER") == 0) {
#define ELSE_NO_FCALL_WRAPPER } else {
#define ENDIF_FCALL_WRAPPER }

IF_USE_FCALL_WRAPPER // EMBARCADERO DELETEME
  /* EMBARCADERO Local: fCall wrapper function lookup and setup if found */
  /* DAWN FIXME: reset globals in hand_function_call cleanup routine.
     See where error exists from hand_function_call, and cleanup there.  */

  /* Search for the symbol "__dbk_fcall_wrapper" in the user's code and 
     if found, set up the CURRENT_FCW and FCW control BPs.
     On success, we'll have:
        fcw_fcallwrapper_val = value of "__dbk_fcall_wrapper"
	real_pc              = reset to (addr of "__dbk_fcall_wrapper" | 1) */
/* EMBARCADERO Local: WORKAROUND against N_SECT Thumb bit bug:
   Save previous g_examine_i_size global disasm variable */
#if defined (TARGET_ARM)
  save_g_examine_i_size = g_examine_i_size;
#endif

  if (fcw_scan_fcallwrapper (&real_pc, sp,
			     &fcw_fcallwrapper_val))
    {
      if (file_log)
	{
	  fprintf_unfiltered (file_log,
			      "fCallWrapper: %s, funcaddr: %s\n",
			      paddr (fcw->fcallwrapper_addr), 
			      paddr (fcw->user_real_pc));
	}
    }
  else
    {
      /* Print a warning and proceed with normal function call
         evaluation.  */
      warning (_("Can't find __dbk_fcall_wrapper function."));
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall will be executed without exception wrapper.\n");
    }
/* EMBARCADERO Local: WORKAROUND against N_SECT Thumb bit bug:
   Restore previous g_examine_i_size global disasm variable */
#if defined (TARGET_ARM)
  g_examine_i_size = save_g_examine_i_size;
#endif

ENDIF_FCALL_WRAPPER // EMBARCADERO DELETEME

  /* Create the dummy stack frame.  Pass in the call dummy address as,
     presumably, the ABI code knows where, in the call dummy, the
     return address should be pointed.  */

  /* EMBARCADERO Local: wrapper function should be defined in RTL */
  if (using_current_fcw ())
    {
      /* We're using the fcall wrapper.  Save off some original call
	 info (we'll use this later to call the user's function), then
	 perform normal argument pushing, but with __dbk_fcall_wrapper
	 as the function, and nargs as 0.  */
      fcw->user_functionval = function;
      fcw->user_nargs = nargs;
      fcw->user_args = args;
      fcw->user_struct_return = struct_return;
      fcw->user_struct_addr = struct_addr;
      if (file_log)
	{
	  fprintf_unfiltered (file_log, "fcw->user_functionval: 0x%lx\n",
			      (long) fcw->user_functionval);
	  fprintf_unfiltered (file_log, "fcw->user_nargs: %d\n",
			      fcw->user_nargs);
	  fprintf_unfiltered (file_log, "fcw->user_args: 0x%lx\n",
			      (long) fcw->user_args);
	  fprintf_unfiltered (file_log,
			      "fCall wrapper setup completed fine.\n");
	}

      /* Use __dbk_fcall_wrapper as the function, and pass nargs
	 as 0.  This will result in: 
	    push bp_addr
	    push struct_addr (if struct_return)
	    push sp */
      gdb_assert (fcw_fcallwrapper_val);
      sp = gdbarch_push_dummy_call (current_gdbarch,
				    fcw_fcallwrapper_val,
				    current_regcache,
				    bp_addr, 0, args, sp,
				    /* KIRILL FIXME: do we really want
				       to pass struct_return here?  
				       I think it shouldn't be pushed
				       until later when we call
				       arm_push_actual_fw_args().  */
				    struct_return, struct_addr);
    }
  else
    {
      if (file_log)
	fprintf_unfiltered (file_log,
			    "fCall will be executed without exception wrapper.\n");
      /* Push the call args.  This will result in: 
	    push bp_addr
	    push struct_addr (if struct_return)
	    for each arg:
	      push arg
	    push sp  */
      sp = gdbarch_push_dummy_call (current_gdbarch, function,
				    current_regcache,
				    bp_addr, nargs, args, sp,
				    struct_return, struct_addr);
    }
  do_cleanups (args_cleanup);

  /* Set up a frame ID for the dummy frame so we can pass it to
     set_momentary_breakpoint.  We need to give the breakpoint a frame
     ID so that the breakpoint code can correctly re-identify the
     dummy breakpoint.  */
  /* Sanity.  The exact same SP value is returned by PUSH_DUMMY_CALL,
     saved as the dummy-frame TOS, and used by unwind_dummy_id to form
     the frame ID's stack address.  */
  dummy_id = frame_id_build (sp, gdbarch_addr_bits_remove (current_gdbarch, bp_addr));

  /* Create a momentary breakpoint at the return address of the
     inferior.  That way it breaks when it returns.  */
  {
    struct breakpoint *bpt;
    struct symtab_and_line sal;
    init_sal (&sal);		/* initialize to zeroes */
    sal.pc = gdbarch_addr_bits_remove (current_gdbarch, bp_addr);
    sal.section = find_pc_overlay (sal.pc);
    /* Sanity.  The exact same SP value is returned by
       PUSH_DUMMY_CALL, saved as the dummy-frame TOS, and used by
       unwind_dummy_id to form the frame ID's stack address.  */
    bpt = set_momentary_breakpoint (sal, dummy_id, bp_call_dummy);
    bpt->disposition = disp_del;
  }

  /* Everything's ready, push all the info needed to restore the
     caller (and identify the dummy-frame) onto the dummy-frame
     stack.  */
  dummy_frame_push (caller_regcache, &dummy_id);
  discard_cleanups (caller_regcache_cleanup);

  /* - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP -
     If you're looking to implement asynchronous dummy-frames, then
     just below is the place to chop this function in two..  */

  /* Now proceed, having reached the desired place.  */
  clear_proceed_status ();
    
  /* Execute a "stack dummy", a piece of code stored in the stack by
     the debugger to be executed in the inferior.

     The dummy's frame is automatically popped whenever that break is
     hit.  If that is the first time the program stops,
     call_function_by_hand returns to its caller with that frame
     already gone and sets RC to 0.
   
     Otherwise, set RC to a non-zero value.  If the called function
     receives a random signal, we do not allow the user to continue
     executing it as this may not work.  The dummy frame is poped and
     we return 1.  If we hit a breakpoint, we leave the frame in place
     and return 2 (the frame will eventually be popped when we do hit
     the dummy end breakpoint).  */

  {
    struct cleanup *old_cleanups = make_cleanup (null_cleanup, 0);
    int saved_async = 0;
    /* EMBARCADERO Local: CPSR register hack for iOS 7 */
    struct cleanup *register_CPSR_HACK_cleanup;

    /* If all error()s out of proceed ended up calling normal_stop
       (and perhaps they should; it already does in the special case
       of error out of resume()), then we wouldn't need this.  */
    make_cleanup (breakpoint_auto_delete_contents, &stop_bpstat);

    disable_watchpoints_before_interactive_call_start ();
    /* APPLE LOCAL checkpointing */
    begin_inferior_call_checkpoints ();
    proceed_to_finish = 1;	/* We want stop_registers, please... */
    proceed_from_hand_call = 1;
    make_cleanup (do_unset_proceed_from_hand_call, NULL);
    /* EMBARCADERO Local: CPSR register hack for iOS 7 */
    register_CPSR_HACK_cleanup = make_cleanup_set_restore_register_CPSR_HACK ();

    if (hand_call_function_hook != NULL)
      hand_call_function_hook ();

    static int hand_call_function_timer = -1;
    struct cleanup *hand_call_cleanup = 
      start_timer (&hand_call_function_timer, "hand-call", "Starting hand-call");
  
    if (target_can_async_p ())
      saved_async = target_async_mask (0);
    
    /* APPLE LOCAL: Make the current ptid available to the
       lower level proceed logic so we can prefer that over
       other stop reasons.  */
    hand_call_ptid = inferior_ptid;
    make_cleanup (do_reset_hand_call_ptid, NULL);

    if (hand_call_function_timeout != 0)
      {
	struct itimerval itval;
	struct gdb_exception e;
	
	itval.it_interval.tv_sec = 0;
	itval.it_interval.tv_usec = 0;
	
	itval.it_value.tv_sec = hand_call_function_timeout/1000000;
	itval.it_value.tv_usec = hand_call_function_timeout% 1000000;
	
	timer_fired = 0;
	signal (SIGALRM, handle_alarm_while_calling);
	setitimer (ITIMER_REAL, &itval, NULL);
	
	TRY_CATCH (e, RETURN_MASK_ERROR)
	  {
	    proceed (real_pc, TARGET_SIGNAL_0, 0);
	  }
	itval.it_value.tv_sec = 0;
	itval.it_value.tv_usec = 0;
	setitimer (ITIMER_REAL, &itval, NULL);
	signal (SIGALRM, SIG_DFL);
	
	if (e.reason != NO_ERROR)
            throw_exception (e);
      }
    else
      {
	timer_fired  = 0;
	proceed (real_pc, TARGET_SIGNAL_0, 0);
      }

    /* Report out the timer: */
    do_cleanups (hand_call_cleanup);

    /* EMBARCADERO Local: CPSR register hack for iOS 7 */
    do_cleanups (register_CPSR_HACK_cleanup);

    hand_call_ptid = minus_one_ptid;

    if (saved_async)
      target_async_mask (saved_async);
    
    /* APPLE LOCAL checkpointing */
    end_inferior_call_checkpoints ();
    enable_watchpoints_after_interactive_call_stop ();
      
    discard_cleanups (old_cleanups);
    proceed_from_hand_call = 0;
  }

  if (timer_fired)
    {
      frame_pop (get_current_frame ());
      error ("User called function timer expired.  Aborting call.");
    }

  if (stopped_by_random_signal 
      || (stop_stack_dummy != STOP_STACK_DUMMY))
    {
      /* Find the name of the function we're about to complain about.  */
      const char *name = NULL;
      {
	struct symbol *symbol = find_pc_function (funaddr);
	if (symbol)
	  name = SYMBOL_PRINT_NAME (symbol);
	else
	  {
	    /* Try the minimal symbols.  */
	    struct minimal_symbol *msymbol = lookup_minimal_symbol_by_pc (funaddr);
	    if (msymbol)
	      name = SYMBOL_PRINT_NAME (msymbol);
	  }
	if (name == NULL)
	  {
	    /* Can't use a cleanup here.  It is discarded, instead use
               an alloca.  */
	    char *tmp = xstrprintf ("at %s", hex_string (funaddr));
	    char *a = alloca (strlen (tmp) + 1);
	    strcpy (a, tmp);
	    xfree (tmp);
	    name = a;
	  }
      }
      /* APPLE LOCAL: Check to see if we were stopped at the ObjC fail breakpoint.  
	 If we are, then unwind if requested & then just fail.  */

      if (stopped_by_random_signal 
	  || objc_pc_at_fail_point (stop_pc) != objc_no_fail)
	{
	  char *errstr = "";

	  if (stopped_by_random_signal)
	    errstr = "The program being debugged was signaled while in a function called from GDB.";
	  else if (objc_pc_at_fail_point (stop_pc) == objc_debugger_mode_fail)
	    errstr = "The program being debugged tried to modify the ObjC runtime at an unsafe "
	      "time while in a function called from gdb";
	  else if (objc_pc_at_fail_point (stop_pc) == objc_exception_thrown)
	    errstr = "The program being debugged hit an ObjC exception while in a function called from gdb.\n\
If you don't want exception throws to interrupt functions called by gdb\n\
set objc-exceptions-interrupt-hand-call-fns to off.";

	  /* We stopped inside the FUNCTION because of a random
	     signal.  Further execution of the FUNCTION is not
	     allowed. */

	  if (unwind_on_signal_p)
	    {
	      /* The user wants the context restored. */

	      /* We must get back to the frame we were before the
		 dummy call. */
	      frame_pop (get_current_frame ());

	      /* FIXME: Insert a bunch of wrap_here; name can be very
		 long if it's a C++ name with arguments and stuff.  */
	      error (_("\
%s\n\
GDB has restored the context to what it was before the call.\n\
To change this behavior use \"set unwindonsignal off\"\n\
Evaluation of the expression containing the function (%s) will be abandoned."),
		     errstr, name);
	    }
	  else
	    {
	      /* The user wants to stay in the frame where we stopped
                 (default).*/
	      /* If we restored the inferior status (via the cleanup),
		 we would print a spurious error message (Unable to
		 restore previously selected frame), would write the
		 registers from the inf_status (which is wrong), and
		 would do other wrong things.  */
	      discard_cleanups (inf_status_cleanup);
	      discard_inferior_status (inf_status);
	      /* FIXME: Insert a bunch of wrap_here; name can be very
		 long if it's a C++ name with arguments and stuff.  */
	      error (_("\
%s\n\
GDB remains in the frame where the signal was received.\n\
To change this behavior use \"set unwindonsignal on\"\n\
Evaluation of the expression containing the function (%s) will be abandoned."),
		     errstr, name);
	    }
	}

      if (stop_stack_dummy == STOP_NONE)
	{
	  /* We hit a breakpoint inside the FUNCTION. */
	  /* If we restored the inferior status (via the cleanup), we
	     would print a spurious error message (Unable to restore
	     previously selected frame), would write the registers
	     from the inf_status (which is wrong), and would do other
	     wrong things.  */
	  discard_cleanups (inf_status_cleanup);
	  discard_inferior_status (inf_status);
	  /* The following error message used to say "The expression
	     which contained the function call has been discarded."
	     It is a hard concept to explain in a few words.  Ideally,
	     GDB would be able to resume evaluation of the expression
	     when the function finally is done executing.  Perhaps
	     someday this will be implemented (it would not be easy).  */
	  /* FIXME: Insert a bunch of wrap_here; name can be very long if it's
	     a C++ name with arguments and stuff.  */
	  error (_("\
The program being debugged stopped while in a function called from GDB.\n\
When the function (%s) is done executing, GDB will silently\n\
stop (instead of continuing to evaluate the expression containing\n\
the function call)."), name);
	}

      /* The above code errors out, so ...  */
      internal_error (__FILE__, __LINE__, _("... should not be here"));
    }

  /* If we get here the called FUNCTION run to completion. */

  /* On normal return, the stack dummy has been popped already.  */
  regcache_cpy_no_passthrough (retbuf, stop_registers);

  /* Restore the inferior status, via its cleanup.  At this stage,
     leave the RETBUF alone.  */
  do_cleanups (inf_status_cleanup);
  /* APPLE LOCAL begin subroutine inlining  */
  inlined_subroutine_restore_after_dummy_call ();
  /* APPLE LOCAL end subroutine inlining  */

  /* EMBARCADERO Local: begin fCall Wrapper */
  /* Handle the case that an exception was caught by the function call
     wrapper.  */
  if (fcw_exception_raised ())
    {
      /* Find the name of the function we're about to complain about.  */
      const char *name;
      struct symbol *symbol = find_pc_function (funaddr);
      if (symbol)
	name = SYMBOL_PRINT_NAME (symbol);
      else
	{
	  /* Try the minimal symbols.  */
	  struct minimal_symbol *msymbol = lookup_minimal_symbol_by_pc (funaddr);
	  if (msymbol)
	    name = SYMBOL_PRINT_NAME (msymbol);
	  else
	    name = "<unknown>";
	}
      error (_("\
An exception was raised during the evaluation of an expression involving \
a call to function (%s). The exception was caught by the Delphi runtime \
and the context was restored."), name);
    }
  /* EMBARCADERO Local: end fCall Wrapper */

  /* Figure out the value returned by the function, return that.  */
  {
    struct value *retval;

    retval = allocate_value (values_type);

    if (TYPE_CODE (target_values_type) != TYPE_CODE_VOID)
      {
	struct gdbarch *gdbarch = current_gdbarch;

	switch (gdbarch_return_value (gdbarch, value_type (function),
				      target_values_type, NULL, NULL, NULL))
	  {
	  case RETURN_VALUE_REGISTER_CONVENTION:
	  case RETURN_VALUE_ABI_RETURNS_ADDRESS:
	  case RETURN_VALUE_ABI_PRESERVES_ADDRESS:
	    gdbarch_return_value (gdbarch, value_type (function), values_type,
				  retbuf, value_contents_raw (retval), NULL);
	    break;
	  case RETURN_VALUE_STRUCT_CONVENTION:
	    VALUE_LVAL (retval) = lval_memory;
	    VALUE_ADDRESS (retval) = struct_addr;
	    set_value_lazy (retval, 1);
	    break;
	  }
      }

    /* APPLE LOCAL: I could piggyback on retbuf_cleanup for this, but
       I'd prefer it to be explicit since this HAS to get cleaned up.  */
    do_cleanups (runtime_cleanup);
    do_cleanups (retbuf_cleanup);
    /* APPLE LOCAL: Now reset this value to the original return
       type.  That way, if the function was returning a typedef,
       the value we are returning will have the same type.  */
    if (retval != NULL)
      deprecated_set_value_type (retval, orig_return_type);

    return retval;
  }
}

struct value *
call_function_by_hand (struct value *function, int nargs, struct value **args)
{
  return hand_function_call (function, NULL, nargs, args, 1);
}

struct value *
call_function_by_hand_expecting_type (struct value *function, struct type *expect_type,
                                      int nargs, struct value **args, int restore_frame)
{
  return hand_function_call (function, expect_type, nargs, args, restore_frame);
}

void _initialize_infcall (void);

void
_initialize_infcall (void)
{
  do_reset_hand_call_ptid ();

  /* EMBARCADERO Local: fCall wrapper */
  init_fcallwrapper_info (current_fcw);

  add_setshow_boolean_cmd ("coerce-float-to-double", class_obscure,
			   &coerce_float_to_double_p, _("\
Set coercion of floats to doubles when calling functions."), _("\
Show coercion of floats to doubles when calling functions"), _("\
Variables of type float should generally be converted to doubles before\n\
calling an unprototyped function, and left alone when calling a prototyped\n\
function.  However, some older debug info formats do not provide enough\n\
information to determine that a function is prototyped.  If this flag is\n\
set, GDB will perform the conversion for a function it considers\n\
unprototyped.\n\
The default is to perform the conversion.\n"),
			   NULL,
			   show_coerce_float_to_double_p,
			   &setlist, &showlist);

  add_setshow_boolean_cmd ("unwindonsignal", no_class,
			   &unwind_on_signal_p, _("\
Set unwinding of stack if a signal is received while in a call dummy."), _("\
Show unwinding of stack if a signal is received while in a call dummy."), _("\
The unwindonsignal lets the user determine what gdb should do if a signal\n\
is received while in a function called from gdb (call dummy).  If set, gdb\n\
unwinds the stack and restore the context to what as it was before the call.\n\
The default is to stop in the frame where the signal was received."),
			   NULL,
			   show_unwind_on_signal_p,
			   &setlist, &showlist);

  add_setshow_boolean_cmd ("objc-exceptions-interrupt-hand-call-fns", class_obscure,
			   &objc_exceptions_interrupt_hand_call, _("\
Set whether hitting an ObjC exception throw interrupts a function called by hand from the debugger."), _("\
Show whether hitting an ObjC exception throw interrupts a function called by hand from the debugger."), _("\
The objc-exceptions-interrupt-hand-call-fns setting lets the user prevent gdb from\n\
stopping on objc exceptions while calling functions by hand.  If the function you\n\
are calling relies on being able to throw and catch exceptions, you may need to turn this\n\
off.  An uncaught exception, however, will unwind past the point where you were stopped\n\
in the debugger, so for the most part you will want to leave this on."),
			   NULL,
			   NULL,
			   &setlist, &showlist);

/* APPLE LOCAL for Greg */
  add_setshow_boolean_cmd ("disable-inferior-function-calls", no_class,
			   &inferior_function_calls_disabled_p, _("\
Set disabling of gdb from running calls in the debugee's context"), _("\
Show disabling of gdb from running calls in the debugee's context"), _("\
The disable-inferior-function-calls setting lets the user prevent gdb from\n\
executing functions in the debugee program's context.  Many gdb commands\n\
can result in functions being run in the target program, e.g. malloc or objc\n\
class lookup functions, when you may not expect.  It is rare that people need\n\
to disable these inferior function calls."),
			   NULL,
			   NULL,
			   &setlist, &showlist);

/* APPLE LOCAL: one way to protect against deadlocking inferior function calls.  */
  add_setshow_zinteger_cmd ("target-function-call-timeout", class_obscure,
			    &hand_call_function_timeout, "\
Set a timeout for gdb issued function calls in the target program.", "	\
Show the timeout for gdb issued function calls in the target program.", " \
The hand-function-call-timeout sets a watchdog timer on calls made by gdb in\n \
the address space of the program being debugged.  The value is in microseconds.\n\
A value of zero disables the timer.",
                            NULL,
                            NULL,
			    &setlist, &showlist);
   
}
