/* Perform an inferior function call, for GDB, the GNU debugger.

   Copyright (C) 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995,
   1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007,
   2008, 2009, 2010, 2011 Free Software Foundation, Inc.

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

#include "defs.h"
#include "breakpoint.h"
#include "tracepoint.h"
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
#include "ada-lang.h"
#include "gdbthread.h"
#include "exceptions.h"
#include "disasm.h"
#include "arch-utils.h"

/* EMBARCADERO Local: File logger */
extern struct ui_file *file_log;

/* If we can't find a function's name from its address,
   we print this instead.  */
#define RAW_FUNCTION_ADDRESS_FORMAT "at 0x%s"
#define RAW_FUNCTION_ADDRESS_SIZE (sizeof (RAW_FUNCTION_ADDRESS_FORMAT) \
                                   + 2 * sizeof (CORE_ADDR))

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
  fprintf_filtered (file,
		    _("Coercion of floats to doubles "
		      "when calling functions is %s.\n"),
		    value);
}

/* This boolean tells what gdb should do if a signal is received while
   in a function called from gdb (call dummy).  If set, gdb unwinds
   the stack and restore the context to what as it was before the
   call.

   The default is to stop in the frame where the signal was received.  */

int unwind_on_signal_p = 0;
static void
show_unwind_on_signal_p (struct ui_file *file, int from_tty,
			 struct cmd_list_element *c, const char *value)
{
  fprintf_filtered (file,
		    _("Unwinding of stack if a signal is "
		      "received while in a call dummy is %s.\n"),
		    value);
}

/* This boolean tells what gdb should do if a std::terminate call is
   made while in a function called from gdb (call dummy).
   As the confines of a single dummy stack prohibit out-of-frame
   handlers from handling a raised exception, and as out-of-frame
   handlers are common in C++, this can lead to no handler being found
   by the unwinder, and a std::terminate call.  This is a false positive.
   If set, gdb unwinds the stack and restores the context to what it
   was before the call.

   The default is to unwind the frame if a std::terminate call is
   made.  */

static int unwind_on_terminating_exception_p = 1;

static void
show_unwind_on_terminating_exception_p (struct ui_file *file, int from_tty,
					struct cmd_list_element *c,
					const char *value)

{
  fprintf_filtered (file,
		    _("Unwind stack if a C++ exception is "
		      "unhandled while in a call dummy is %s.\n"),
		    value);
}

/* Perform the standard coercions that are specified
   for arguments to be passed to C or Ada functions.

   If PARAM_TYPE is non-NULL, it is the expected parameter type.
   IS_PROTOTYPED is non-zero if the function declaration is prototyped.
   SP is the stack pointer were additional data can be pushed (updating
   its value as needed).  */

static struct value *
value_arg_coerce (struct gdbarch *gdbarch, struct value *arg,
		  struct type *param_type, int is_prototyped, CORE_ADDR *sp)
{
  const struct builtin_type *builtin = builtin_type (gdbarch);
  struct type *arg_type = check_typedef (value_type (arg));
  struct type *type
    = param_type ? check_typedef (param_type) : arg_type;

  /* Perform any Ada-specific coercion first.  */
  if (current_language->la_language == language_ada)
    arg = ada_convert_actual (arg, type);

  /* Force the value to the target if we will need its address.  At
     this point, we could allocate arguments on the stack instead of
     calling malloc if we knew that their addresses would not be
     saved by the called function.  */
  arg = value_coerce_to_target (arg);

  switch (TYPE_CODE (type))
    {
    case TYPE_CODE_REF:
      {
	struct value *new_value;

	if (TYPE_CODE (arg_type) == TYPE_CODE_REF)
	  return value_cast_pointers (type, arg);

	/* Cast the value to the reference's target type, and then
	   convert it back to a reference.  This will issue an error
	   if the value was not previously in memory - in some cases
	   we should clearly be allowing this, but how?  */
	new_value = value_cast (TYPE_TARGET_TYPE (type), arg);
	new_value = value_ref (new_value);
	return new_value;
      }
    case TYPE_CODE_INT:
    case TYPE_CODE_CHAR:
    case TYPE_CODE_BOOL:
    case TYPE_CODE_ENUM:
      /* If we don't have a prototype, coerce to integer type if necessary.  */
      if (!is_prototyped)
	{
	  if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin->builtin_int))
	    type = builtin->builtin_int;
	}
      /* Currently all target ABIs require at least the width of an integer
         type for an argument.  We may have to conditionalize the following
         type coercion for future targets.  */
      if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin->builtin_int))
	type = builtin->builtin_int;
      break;
    case TYPE_CODE_FLT:
      if (!is_prototyped && coerce_float_to_double_p)
	{
	  if (TYPE_LENGTH (type) < TYPE_LENGTH (builtin->builtin_double))
	    type = builtin->builtin_double;
	  else if (TYPE_LENGTH (type) > TYPE_LENGTH (builtin->builtin_double))
	    type = builtin->builtin_long_double;
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

/* Return the return type of a function with its first instruction exactly at
   the PC address.  Return NULL otherwise.  */

static struct type *
find_function_return_type (CORE_ADDR pc)
{
  struct symbol *sym = find_pc_function (pc);

  if (sym != NULL && BLOCK_START (SYMBOL_BLOCK_VALUE (sym)) == pc
      && SYMBOL_TYPE (sym) != NULL)
    return TYPE_TARGET_TYPE (SYMBOL_TYPE (sym));

  return NULL;
}

/* Determine a function's address and its return type from its value.
   Calls error() if the function is not valid for calling.  */

CORE_ADDR
find_function_addr (struct value *function, struct type **retval_type)
{
  struct type *ftype = check_typedef (value_type (function));
  struct gdbarch *gdbarch = get_type_arch (ftype);
  struct type *value_type = NULL;
  /* Initialize it just to avoid a GCC false warning.  */
  CORE_ADDR funaddr = 0;

  /* If it's a member function, just look at the function
     part of it.  */

  /* Determine address to call.  */
  if (TYPE_CODE (ftype) == TYPE_CODE_FUNC
      || TYPE_CODE (ftype) == TYPE_CODE_METHOD)
    funaddr = value_address (function);
  else if (TYPE_CODE (ftype) == TYPE_CODE_PTR)
    {
      funaddr = value_as_address (function);
      ftype = check_typedef (TYPE_TARGET_TYPE (ftype));
      if (TYPE_CODE (ftype) == TYPE_CODE_FUNC
	  || TYPE_CODE (ftype) == TYPE_CODE_METHOD)
	funaddr = gdbarch_convert_from_func_ptr_addr (gdbarch, funaddr,
						      &current_target);
    }
  if (TYPE_CODE (ftype) == TYPE_CODE_FUNC
      || TYPE_CODE (ftype) == TYPE_CODE_METHOD)
    {
      if (TYPE_CODE (TYPE_TARGET_TYPE (ftype)) == TYPE_CODE_TYPEDEF)
	value_type = TYPE_TARGET_TYPE (TYPE_TARGET_TYPE (ftype));
      else
	value_type = TYPE_TARGET_TYPE (ftype);

      if (TYPE_GNU_IFUNC (ftype))
	{
	  funaddr = gnu_ifunc_resolve_addr (gdbarch, funaddr);

	  /* Skip querying the function symbol if no RETVAL_TYPE has been
	     asked for.  */
	  if (retval_type)
	    value_type = find_function_return_type (funaddr);
	}
    }
  else if (TYPE_CODE (ftype) == TYPE_CODE_INT)
    {
      /* Handle the case of functions lacking debugging info.
         Their values are characters since their addresses are char.  */
      if (TYPE_LENGTH (ftype) == 1)
	funaddr = value_as_address (value_addr (function));
      else
	{
	  /* Handle function descriptors lacking debug info.  */
	  int found_descriptor = 0;

	  funaddr = 0;	/* pacify "gcc -Werror" */
	  if (VALUE_LVAL (function) == lval_memory)
	    {
	      CORE_ADDR nfunaddr;

	      funaddr = value_as_address (value_addr (function));
	      nfunaddr = funaddr;
	      funaddr = gdbarch_convert_from_func_ptr_addr (gdbarch, funaddr,
							    &current_target);
	      if (funaddr != nfunaddr)
		found_descriptor = 1;
	    }
	  if (!found_descriptor)
	    /* Handle integer used as address of a function.  */
	    funaddr = (CORE_ADDR) value_as_long (function);
	}
    }
  else
    error (_("Invalid data type for function to be called."));

  if (retval_type != NULL)
    *retval_type = value_type;
  return funaddr + gdbarch_deprecated_function_start_offset (gdbarch);
}

/* For CALL_DUMMY_ON_STACK, push a breakpoint sequence that the called
   function returns to.  */

static CORE_ADDR
push_dummy_code (struct gdbarch *gdbarch,
		 CORE_ADDR sp, CORE_ADDR funaddr,
		 struct value **args, int nargs,
		 struct type *value_type,
		 CORE_ADDR *real_pc, CORE_ADDR *bp_addr,
		 struct regcache *regcache)
{
  gdb_assert (gdbarch_push_dummy_code_p (gdbarch));

  return gdbarch_push_dummy_code (gdbarch, sp, funaddr,
				  args, nargs, value_type, real_pc, bp_addr,
				  regcache);
}

/* Fetch the name of the function at FUNADDR.
   This is used in printing an error message for call_function_by_hand.
   BUF is used to print FUNADDR in hex if the function name cannot be
   determined.  It must be large enough to hold formatted result of
   RAW_FUNCTION_ADDRESS_FORMAT.  */

static const char *
get_function_name (CORE_ADDR funaddr, char *buf, int buf_size)
{
  {
    struct symbol *symbol = find_pc_function (funaddr);

    if (symbol)
      return SYMBOL_PRINT_NAME (symbol);
  }

  {
    /* Try the minimal symbols.  */
    struct minimal_symbol *msymbol = lookup_minimal_symbol_by_pc (funaddr);

    if (msymbol)
      return SYMBOL_PRINT_NAME (msymbol);
  }

  {
    char *tmp = xstrprintf (_(RAW_FUNCTION_ADDRESS_FORMAT),
                            hex_string (funaddr));

    gdb_assert (strlen (tmp) + 1 <= buf_size);
    strcpy (buf, tmp);
    xfree (tmp);
    return buf;
  }
}

/* Subroutine of call_function_by_hand to simplify it.
   Start up the inferior and wait for it to stop.
   Return the exception if there's an error, or an exception with
   reason >= 0 if there's no error.

   This is done inside a TRY_CATCH so the caller needn't worry about
   thrown errors.  The caller should rethrow if there's an error.  */

static struct gdb_exception
run_inferior_call (struct thread_info *call_thread, CORE_ADDR real_pc)
{
  volatile struct gdb_exception e;
  int saved_async = 0;
  int saved_in_infcall = call_thread->control.in_infcall;
  ptid_t call_thread_ptid = call_thread->ptid;
  char *saved_target_shortname = xstrdup (target_shortname);

  call_thread->control.in_infcall = 1;

  clear_proceed_status ();

  disable_watchpoints_before_interactive_call_start ();

  /* We want stop_registers, please...  */
  call_thread->control.proceed_to_finish = 1;

  if (target_can_async_p ())
    saved_async = target_async_mask (0);

  TRY_CATCH (e, RETURN_MASK_ALL)
    proceed (real_pc, TARGET_SIGNAL_0, 0);

  /* At this point the current thread may have changed.  Refresh
     CALL_THREAD as it could be invalid if its thread has exited.  */
  call_thread = find_thread_ptid (call_thread_ptid);

  /* Don't restore the async mask if the target has changed,
     saved_async is for the original target.  */
  if (saved_async
      && strcmp (saved_target_shortname, target_shortname) == 0)
    target_async_mask (saved_async);

  enable_watchpoints_after_interactive_call_stop ();

  /* Call breakpoint_auto_delete on the current contents of the bpstat
     of inferior call thread.
     If all error()s out of proceed ended up calling normal_stop
     (and perhaps they should; it already does in the special case
     of error out of resume()), then we wouldn't need this.  */
  if (e.reason < 0)
    {
      if (call_thread != NULL)
	breakpoint_auto_delete (call_thread->control.stop_bpstat);
    }

  if (call_thread != NULL)
    call_thread->control.in_infcall = saved_in_infcall;

  xfree (saved_target_shortname);

  return e;
}

/* A cleanup function that calls delete_std_terminate_breakpoint.  */
static void
cleanup_delete_std_terminate_breakpoint (void *ignore)
{
  delete_std_terminate_breakpoint ();
}

/* EMBARCADERO Local: set in solib.c */
CORE_ADDR nativemain_addr = 0;

/* EMBARCADERO Local: Set to False for getting real contents of .text 
section directly from device instead of cached local debug libs */
extern int trust_readonly;

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
push_current_fcw (CORE_ADDR fcallwrapper_addr)
{
  struct fcallwrapper_info *fcw = XMALLOC (struct fcallwrapper_info);
  init_fcallwrapper_info (fcw);
  fcw->next = current_fcw;
  fcw->fcallwrapper_addr = fcallwrapper_addr;
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
  /* Free malloced space used for fCall arguments, if any. */
  if (fcw->args_to_delete)
    xfree(fcw->args_to_delete);

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
      fcw->args_to_delete = NULL;
      fcw->fcallwrapper_addr = 0;
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
set_fcw_breakpoint (struct gdbarch *gdbarch, CORE_ADDR bp_addr,
		    const char *bp_name, CORE_ADDR sp)
{
  struct breakpoint *bpt;
  struct symtab_and_line sal;
  struct frame_id dummy_id;
  char buf[64];
	
  init_sal (&sal);		/* initialize to zeroes */
  sal.pspace = current_program_space;
  sal.pc = bp_addr;
  /* Note: iosgdb also does:
     sal.pc = gdbarch_addr_bits_remove (current_gdbarch, sal.pc);  */
  if (file_log)
    fprintf_unfiltered (file_log, "Setting %s BP at: %s\n",
			bp_name, paddress (gdbarch, sal.pc));
  sal.explicit_pc = 1;
  sal.section = find_pc_overlay (sal.pc);
  dummy_id = frame_id_build (sp, sal.pc);
  bpt = set_momentary_breakpoint (gdbarch, sal, dummy_id, bp_call_dummy);
  bpt->thread = -1;
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
			    paddress (get_current_arch(), bpt->loc->address));
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
			    paddress (get_current_arch(), bpt->loc->address));

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
			    paddress (get_current_arch(), bpt->loc->address));
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

/* Check if the RTL will permit us to call functions:

   Called before a current fcw structure for the fCall has been created.

   For Pascal, search for the fCall wrapper function symbol "dbkFCallWrapperAddr"
   in the user's code.

   Return 1 on success, else 0.  */

static int
fcw_can_call_function (struct gdbarch *gdbarch)
{
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

   Called before a current fcw structure for the fCall has been created.

   Search for the RTL's initialization flag symbol "dbk_RTL_initialized" and
   fail if not found or not set to 1.

   Search for the fCall wrapper function symbol "__dbk_fcall_wrapper"
   in the user's code and return the address if found.

    On success, return:
	*FCALLWRAPPER_ADDR_P = address of "__dbk_fcall_wrapper"
    Return 1 on success, else 0.  */

static int
fcw_can_use_fcallwrapper (struct gdbarch *gdbarch,
			  CORE_ADDR *fcallwrapper_addr_p)
{
  CORE_ADDR RTLinitialized_addr = 0;
  CORE_ADDR fcallwrapper_addr = 0;
  struct minimal_symbol *RTLinitialized_sym = NULL;
  struct minimal_symbol *fcallwrapper_sym = NULL;
  int32_t RTLinitialized_flag = 0;

  /* Init output to 0.  */
  *fcallwrapper_addr_p = 0;

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
			paddress (gdbarch, RTLinitialized_addr));
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
			paddress (gdbarch, fcallwrapper_addr));

  /* Return the adress. */
  *fcallwrapper_addr_p = fcallwrapper_addr;
  return 1;
}

/* fCall Wrapper control points scanner:
  
   Prepare the CURRENT_FCW and set the FCW control BPs.

   SP is the user's stack address.
   REAL_PC_P is a pointer to the user's PC.
   FCALLWRAPPER_ADDR is the address of the RTL's fCall wrapper function
        symbol "__dbk_fcall_wrapper"

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
	*REAL_PC_P          = reset to addr of "__dbk_fcall_wrapper"
    Return 1 on success, else 0.  */

static int
fcw_scan_fcallwrapper (struct gdbarch *gdbarch, 
		       CORE_ADDR *real_pc_p, CORE_ADDR sp,
		       struct value **fcallwrapper_val_p)
{
  struct fcallwrapper_info *fcw = get_current_fcw ();
  CORE_ADDR fcw_ReadyToPushPoint = 0;
  CORE_ADDR fcw_ResultFetchPoint = 0;
  CORE_ADDR fcw_CatchPoint = 0;
  CORE_ADDR fcallwrapper_low, fcallwrapper_high;
  CORE_ADDR real_pc = *real_pc_p;
  struct value *fcallwrapper_val = NULL;

  /* Init output to 0.  */
  *fcallwrapper_val_p = NULL;

  gdb_assert (using_current_fcw () && fcw->fcallwrapper_addr);

  // FIXME: why aren't we just using fcw->fcallwrapper_addr here?
  fcallwrapper_val = find_function_in_inferior ("__dbk_fcall_wrapper", NULL);
  if (!fcallwrapper_val)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to determine value of __dbk_fcall_wrapper.\n");
      fcw->fcallwrapper_addr = 0;
      return 0;
    }

  /* Find reliable fCall wrapper function range.  */
  find_pc_partial_function (fcw->fcallwrapper_addr, NULL,
			    &fcallwrapper_low, &fcallwrapper_high);
  while (fcallwrapper_low < fcallwrapper_high)
    {
      struct ui_file *disasm_mem_dump;
      char* disasm_text; 
      long disasm_text_length;
      int insn_length = 0;

      if (file_log)
	fprintf_unfiltered (file_log, "%s:\t",
			    paddress (gdbarch, fcallwrapper_low));
      disasm_mem_dump = mem_fileopen ();
      insn_length = gdb_print_insn (gdbarch,
				    fcallwrapper_low, 
				    disasm_mem_dump, 
				    NULL);
      disasm_text = ui_file_xstrdup (disasm_mem_dump, &disasm_text_length);

      /* Check for fCall wrapper __dbkFCallArgs calls.  */
      if ((strstr(disasm_text, "Sysinit.__dbkFCallArgs") != NULL)
	  && !fcw_ReadyToPushPoint)
	{
	  /* First call to __dbkFCallArgs found.  */
	  if (file_log)
	    fprintf_unfiltered (file_log, "%s:\t%s\n", "ReadyToPushPoint",
				disasm_text);
	  fcw_ReadyToPushPoint = fcallwrapper_low;
	  fcw_ResultFetchPoint = fcallwrapper_low + insn_length;
	}
      else if ((strstr(disasm_text, "Sysinit.__dbkFCallArgs") != NULL)
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
      trust_readonly = 0;
      while (fcallwrapper_low < fcallwrapper_high)
	{
	  fprintf_unfiltered (file_log, "%s:\t",
			      paddress (gdbarch, fcallwrapper_low));
	  fcallwrapper_low = fcallwrapper_low
			      + gdb_print_insn (gdbarch, fcallwrapper_low,
						file_log, NULL);
	  fprintf_unfiltered (file_log, "\n");
	}
      trust_readonly = 1;
    }
#endif /* 0 */

  /* Make sure we found all our control points.  */
  if (!fcw_ReadyToPushPoint || !fcw_CatchPoint)
    {
      if (file_log)
	fprintf_unfiltered (file_log, "Unable to locate call instructions in function call wrapper.\n");
      fcw->fcallwrapper_addr = 0;
      return 0;
    }

  /* Set a few values in the current_fcw.  */
  /* The user's return addr is where we will fetch results.  */
  fcw->user_lr = fcw_ResultFetchPoint;

  fcw->user_real_pc = real_pc;
  real_pc = fcw->fcallwrapper_addr;

  /* Set temporary BPs at fCall wrapper control points:
     * fcw_ReadyToPushPoint - fCall wrapper arguments push point
     * fcw_CatchPoint - fCall Wrapper catch point
     * fcw_ResultFetchPoint - fCall Wrapper get result point
     We'll recognize these by name when we hit them.  */
      
  fcw->ReadyToPushPoint_bpt
    = set_fcw_breakpoint (gdbarch, fcw_ReadyToPushPoint,
			  "fCallWrapperReadyToArgPush", sp);
  fcw->CatchPoint_bpt
    = set_fcw_breakpoint (gdbarch, fcw_CatchPoint,
			  "fCallWrapperCatch", sp);
  fcw->ResultFetchPoint_bpt
    = set_fcw_breakpoint (gdbarch, fcw_ResultFetchPoint,
			  "fCallWrapperGetResult", sp);

  *real_pc_p = real_pc;
  *fcallwrapper_val_p = fcallwrapper_val;

  if (file_log)
    {
      fprintf_unfiltered (file_log,
			  "fCallWrapper: %s, funcaddr: %s\n", 
			  paddress (gdbarch, fcw->fcallwrapper_addr), 
			  paddress (gdbarch, fcw->user_real_pc));
    }
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

   ARGS is modified to contain coerced values.  */

struct value *
call_function_by_hand (struct value *function, int nargs, struct value **args)
{
  CORE_ADDR sp;
  struct type *values_type, *target_values_type;
  unsigned char struct_return = 0, lang_struct_return = 0;
  CORE_ADDR struct_addr = 0;
  struct infcall_control_state *inf_status;
  struct cleanup *inf_status_cleanup;
  struct infcall_suspend_state *caller_state;
  CORE_ADDR funaddr;
  CORE_ADDR real_pc;
  struct type *ftype = check_typedef (value_type (function));
  CORE_ADDR bp_addr;
  struct frame_id dummy_id;
  struct cleanup *args_cleanup;
  struct frame_info *frame;
  struct gdbarch *gdbarch;
  struct cleanup *terminate_bp_cleanup;
  ptid_t call_thread_ptid;
  struct gdb_exception e;
  char name_buf[RAW_FUNCTION_ADDRESS_SIZE];
  /* EMBARCADERO Local: fCall Wrapper */
  struct fcallwrapper_info *fcw;
  struct value *fcw_fcallwrapper_val = NULL;
  CORE_ADDR fcallwrapper_addr = 0;
  struct cleanup *fcw_cleanup;

  if ((TYPE_CODE (ftype) == TYPE_CODE_PTR)
      || (TYPE_CODE (ftype) == TYPE_CODE_METHOD))
    ftype = check_typedef (TYPE_TARGET_TYPE (ftype));

  if (!target_has_execution)
    noprocess ();

  if (get_traceframe_number () >= 0)
    error (_("May not call functions while looking at trace frames."));

  frame = get_current_frame ();
  gdbarch = get_frame_arch (frame);

  /* EMBARCADERO LOCAL begin: fCall Wrapper */
  /* See if the RTL will permit us to call functions.  */
  if (!fcw_can_call_function (gdbarch))
  {
    error (_("Unable to perform protected function calls, function call aborted."));
  }
  /* EMBARCADERO LOCAL end: fCall Wrapper */

  if (!gdbarch_push_dummy_call_p (gdbarch))
    error (_("This target does not support function calls."));

  /* EMBARCADERO Local begin calling conventions */
  /* See if this function calling convention is supported.  
     FIXME: this should really be in the target vector.  */
  if (!gdbarch_calling_convention_supported (gdbarch, function))
    {
      char *sym_name;
      const char *ccstr;
      funaddr = find_function_addr (function, &values_type);
      find_pc_partial_function (funaddr, &sym_name, NULL, NULL);
      ccstr = gdbarch_calling_convention_string (gdbarch, function);

      error ("Unable to call function \"%s\": "
	     "calling convention \"%s\" not supported",
	     sym_name ? sym_name : "<unknown>",
	     ccstr ? ccstr : "<unknown>");
    }
  /* EMBARCADERO Local end calling conventions */

  /* EMBARCADERO Local: fCall Wrapper init */
  /* See if we can use the Delphi RTL's fCall wrapper.  If we can,
     fcallwrapper_addr will be set to the address.  */
  if (!fcw_can_use_fcallwrapper (gdbarch, &fcallwrapper_addr))
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
  push_current_fcw (fcallwrapper_addr);
  fcw_cleanup = make_cleanup (pop_current_fcw_cleanup, NULL);
  fcw = get_current_fcw ();
  gdb_assert (fcw);

  /* A cleanup for the inferior status.
     This is only needed while we're preparing the inferior function call.  */
  inf_status = save_infcall_control_state ();
  inf_status_cleanup
    = make_cleanup_restore_infcall_control_state (inf_status);

  /* Save the caller's registers and other state associated with the
     inferior itself so that they can be restored once the
     callee returns.  To allow nested calls the registers are (further
     down) pushed onto a dummy frame stack.  Include a cleanup (which
     is tossed once the regcache has been pushed).  */
  caller_state = save_infcall_suspend_state ();
  make_cleanup_restore_infcall_suspend_state (caller_state);

  /* Ensure that the initial SP is correctly aligned.  */
  {
    CORE_ADDR old_sp = get_frame_sp (frame);

    if (gdbarch_frame_align_p (gdbarch))
      {
	sp = gdbarch_frame_align (gdbarch, old_sp);
	/* NOTE: cagney/2003-08-13: Skip the "red zone".  For some
	   ABIs, a function can use memory beyond the inner most stack
	   address.  AMD64 called that region the "red zone".  Skip at
	   least the "red zone" size before allocating any space on
	   the stack.  */
	if (gdbarch_inner_than (gdbarch, 1, 2))
	  sp -= gdbarch_frame_red_zone_size (gdbarch);
	else
	  sp += gdbarch_frame_red_zone_size (gdbarch);
	/* Still aligned?  */
	gdb_assert (sp == gdbarch_frame_align (gdbarch, sp));
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
	    if (gdbarch_inner_than (gdbarch, 1, 2))
	      /* Stack grows down.  */
	      sp = gdbarch_frame_align (gdbarch, old_sp - 1);
	    else
	      /* Stack grows up.  */
	      sp = gdbarch_frame_align (gdbarch, old_sp + 1);
	  }
	/* SP may have underflown address zero here from OLD_SP.  Memory access
	   functions will probably fail in such case but that is a target's
	   problem.  */
      }
    else
      /* FIXME: cagney/2002-09-18: Hey, you loose!

	 Who knows how badly aligned the SP is!

	 If the generic dummy frame ends up empty (because nothing is
	 pushed) GDB won't be able to correctly perform back traces.
	 If a target is having trouble with backtraces, first thing to
	 do is add FRAME_ALIGN() to the architecture vector.  If that
	 fails, try dummy_id().

         If the ABI specifies a "Red Zone" (see the doco) the code
         below will quietly trash it.  */
      sp = old_sp;
  }

  funaddr = find_function_addr (function, &values_type);
  if (!values_type)
    values_type = builtin_type (gdbarch)->builtin_int;

  CHECK_TYPEDEF (values_type);

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

  /* EMBARCADERO Local begin: Delphi struct return */
  if (current_language->la_language == language_pascal)
    {
      /* Ask arch, then language if function result type is supported */
      if (using_struct_return (gdbarch, value_type (function), values_type))
	{    
	  if (language_pass_by_reference (values_type))
	    {
	      lang_struct_return = 1;
	      struct_return = 1;
	      /* Tell the target specific argument pushing routine not to
	      expect a value.  */
	      target_values_type = values_type;
	    }
	  else
	    error ("Passing of result pointer not supported for function result type.");
	}
      else
	target_values_type = values_type;
    }
  else
  /* EMBARCADERO Local end: Delphi struct return */
    {
      if (language_pass_by_reference (values_type))
        {
          lang_struct_return = 1;

          /* Tell the target specific argument pushing routine not to
	     expect a value.  */
          target_values_type = builtin_type (gdbarch)->builtin_void;
        }
      else
        {
          struct_return = using_struct_return (gdbarch,
					       value_type (function), values_type);
          target_values_type = values_type;
        }
    }

  /* Determine the location of the breakpoint (and possibly other
     stuff) that the called function will return to.  The SPARC, for a
     function returning a structure or union, needs to make space for
     not just the breakpoint but also an extra word containing the
     size (?) of the structure being passed.  */

  /* The actual breakpoint (at BP_ADDR) is inserted separatly so there
     is no need to write that out.  */

  switch (gdbarch_call_dummy_location (gdbarch))
    {
    case ON_STACK:
      sp = push_dummy_code (gdbarch, sp, funaddr,
				args, nargs, target_values_type,
				&real_pc, &bp_addr, get_current_regcache ());
      break;
    case AT_ENTRY_POINT:
      {
	CORE_ADDR dummy_addr;

	real_pc = funaddr;
	/* EMBARCADERO Local: Use resolved _NativeMain() as entry_point_address 
	   for Android target because usual entry point manner does not work 
	   in case main app module is solib by itself - Android specific only. */
	if (!is_target_linux_android())
	  dummy_addr = entry_point_address ();
	else
	  dummy_addr = nativemain_addr;
	if (!dummy_addr)
	  error (_("Can't find reliable fCall return address in process."));

	/* A call dummy always consists of just a single breakpoint, so
	   its address is the same as the address of the dummy.  */
	bp_addr = dummy_addr;
	break;
      }
    case AT_SYMBOL:
      /* Some executables define a symbol __CALL_DUMMY_ADDRESS whose
	 address is the location where the breakpoint should be
	 placed.  Once all targets are using the overhauled frame code
	 this can be deleted - ON_STACK is a better option.  */
      {
	struct minimal_symbol *sym;
	CORE_ADDR dummy_addr;

	sym = lookup_minimal_symbol ("__CALL_DUMMY_ADDRESS", NULL, NULL);
	real_pc = funaddr;
	if (sym)
	  {
	    dummy_addr = SYMBOL_VALUE_ADDRESS (sym);
	    /* Make certain that the address points at real code, and not
	       a function descriptor.  */
	    dummy_addr = gdbarch_convert_from_func_ptr_addr (gdbarch,
							     dummy_addr,
							     &current_target);
	  }
	else
	  dummy_addr = entry_point_address ();
	/* A call dummy always consists of just a single breakpoint,
	   so it's address is the same as the address of the dummy.  */
	bp_addr = dummy_addr;
	break;
      }
    default:
      internal_error (__FILE__, __LINE__, _("bad switch"));
    }

  /* EMBARCADERO Local: Use original function type for arg count check
     - ftype may be function result target type here */
  if ((TYPE_CODE (check_typedef (value_type (function))) == TYPE_CODE_PTR)
      || (TYPE_CODE (check_typedef (value_type (function))) == TYPE_CODE_METHOD))
    {
	  if (nargs < TYPE_NFIELDS (check_typedef (value_type (function))))
		error (_("Too few arguments in function call."));
    }
  else
    {
	  if (nargs < TYPE_NFIELDS (ftype))
		error (_("Too few arguments in function call."));
    }

  {
    int i;

    for (i = nargs - 1; i >= 0; i--)
      {
	int prototyped;
	struct type *param_type;

	/* EMBARCADERO Local: Use original function type for param_type 
		and prototype check - ftype may be function result target type here already, 
		i.e != original function type */
	if ((TYPE_CODE (check_typedef (value_type (function))) == TYPE_CODE_PTR)
	    || (TYPE_CODE (check_typedef (value_type (function))) == TYPE_CODE_METHOD))
	  {
		/* FIXME drow/2002-05-31: Should just always mark methods as
		   prototyped.  Can we respect TYPE_VARARGS?  Probably not.  */
		if (TYPE_CODE (check_typedef (value_type (function))) == TYPE_CODE_METHOD)
		  prototyped = 1;
		else if (i < TYPE_NFIELDS (check_typedef (value_type (function))))
		  prototyped = TYPE_PROTOTYPED (check_typedef (value_type (function)));
		else
		  prototyped = 0;

		if (i < TYPE_NFIELDS (check_typedef (value_type (function))))
		  param_type = TYPE_FIELD_TYPE (check_typedef (value_type (function)), i);
		else
		  param_type = NULL;
	  }
	else
	  {
		/* FIXME drow/2002-05-31: Should just always mark methods as
		   prototyped.  Can we respect TYPE_VARARGS?  Probably not.  */
		if (TYPE_CODE (ftype) == TYPE_CODE_METHOD)
		  prototyped = 1;
		else if (i < TYPE_NFIELDS (ftype))
		  prototyped = TYPE_PROTOTYPED (ftype);
		else
		  prototyped = 0;

		if (i < TYPE_NFIELDS (ftype))
		  param_type = TYPE_FIELD_TYPE (ftype, i);
		else
		  param_type = NULL;
	  }

	/* EMBARCADERO LOCAL: begin Delphi ABI */
	/* Are we passing a value using a structure reference or a normal
	   value?  */
	if (param_type && using_pass_value_as_reference (gdbarch, function, param_type))
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
	    struct type *arg_type
	      = check_typedef (value_enclosing_type (args[i]));

	    len = TYPE_LENGTH (arg_type);

	    if (gdbarch_inner_than (gdbarch, 1, 2))
	      {
		/* Stack grows downward.  Align STRUCT_ADDR and SP after
		   making space for the return value.  */
		sp -= len;
		if (gdbarch_frame_align_p (gdbarch))
		  sp = gdbarch_frame_align (gdbarch, sp);
		addr = sp;
	      }
	    else
	      {
		/* Stack grows upward.  Align the frame, allocate space, and
		   then again, re-align the frame???  */
		if (gdbarch_frame_align_p (gdbarch))
		  sp = gdbarch_frame_align (gdbarch, sp);
		addr = sp;
		sp += len;
		if (gdbarch_frame_align_p (gdbarch))
		  sp = gdbarch_frame_align (gdbarch, sp);
	      }

	    /* Push the structure.  */
	    write_memory (addr, value_contents_all (args[i]), len);
	    /* The value we're going to pass is the address of the
	       thing we just pushed.  */
	    args[i] = value_from_pointer (lookup_pointer_type (arg_type),
					  addr);
	  }
	else
	  args[i] = value_arg_coerce (gdbarch, args[i],
				      param_type, prototyped, &sp);
	/* EMBARCADERO LOCAL: end Delphi ABI */
      }
  }

  /* Reserve space for the return structure to be written on the
     stack, if necessary.  Make certain that the value is correctly
     aligned.  */

  if (struct_return || lang_struct_return)
    {
      int len;

      /* EMBARCADERO Local begin: Delphi struct return */
      if (current_language->la_language == language_pascal)
        {
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
        }
      else
      /* EMBARCADERO Local end: Delphi struct return */
        len = TYPE_LENGTH (values_type);

      if (gdbarch_inner_than (gdbarch, 1, 2))
	{
	  /* Stack grows downward.  Align STRUCT_ADDR and SP after
             making space for the return value.  */
          /* EMBARCADERO Local begin: Delphi struct return */
          if (current_language->la_language == language_pascal)
            {
	      /* KIRILL FIXME TODO: We should calculate struct_addr 
		 with taking care about autorefcounting - i.e. 
		 temp ptrs must be kept until frame changed */
	      /* was: sp -= len; */
	      sp = sp - len - 0x10000; /* 64k */
	    }
	  else
          /* EMBARCADERO Local end: Delphi struct return */
	    sp -= len;

	  if (gdbarch_frame_align_p (gdbarch))
	    sp = gdbarch_frame_align (gdbarch, sp);
	  struct_addr = sp;
	}
      else
	{
	  /* Stack grows upward.  Align the frame, allocate space, and
             then again, re-align the frame???  */
	  if (gdbarch_frame_align_p (gdbarch))
	    sp = gdbarch_frame_align (gdbarch, sp);
	  struct_addr = sp;
	  sp += len;
	  if (gdbarch_frame_align_p (gdbarch))
	    sp = gdbarch_frame_align (gdbarch, sp);
	}
    }

  /* EMBARCADERO Local: fCall wrapper function lookup and setup if found */
  /* DAWN FIXME: reset globals in hand_function_call cleanup routine.
     See where error exists from hand_function_call, and cleanup there.  */

  /* If use the RTL's fCall wrapper, scan the symbol "__dbk_fcall_wrapper" in
     the user's code and set up the CURRENT_FCW and FCW control BPs.
     On success, we'll have:
        fcw_fcallwrapper_val = value of "__dbk_fcall_wrapper"
	real_pc              = reset to addr of "__dbk_fcall_wrapper" */
  if (using_current_fcw ())
    {
      if (!fcw_scan_fcallwrapper (gdbarch, &real_pc, sp,
			          &fcw_fcallwrapper_val))
        {
          if (file_log)
	    fprintf_unfiltered (file_log,
			        "fcw_scan_fcallwrapper failed - executing fCall without exception wrapper.\n");
          /* Print a warning and proceed with normal function call
             evaluation.  */
          warning (_("The function call will be executed without the RTL's exception wrapper."));
        }
    }

  /* EMBARCADERO Local begin: Delphi struct return */
  if (current_language->la_language == language_pascal)
    args_cleanup = make_cleanup (null_cleanup, NULL);
  else
  /* EMBARCADERO Local end: Delphi struct return */
    {
      if (lang_struct_return)
        {
          struct value **new_args;

          /* Add the new argument to the front of the argument list.  */
          new_args = xmalloc (sizeof (struct value *) * (nargs + 1));
          new_args[0] = value_from_pointer (lookup_pointer_type (values_type),
					    struct_addr);
          memcpy (&new_args[1], &args[0], sizeof (struct value *) * nargs);
          args = new_args;
          nargs++;
	  /* EMBARCADERO Local: begin fCall wrapper */
	  /* If we're using te RTL's fCall wrapper, don't delete the args
	     until we're ready to clean up the fcw structure, or else the
	     memory will get freed before we're ready to push the arguments. */
	  if (using_current_fcw ())
	    {
	      args_cleanup = make_cleanup (null_cleanup, NULL);
	      fcw->args_to_delete = args;
	    }
	  else
	  /* EMBARCADERO Local: end fCall wrapper */
            args_cleanup = make_cleanup (xfree, args);
        }
      else
        args_cleanup = make_cleanup (null_cleanup, NULL);
    }

  /* Create the dummy stack frame.  Pass in the call dummy address as,
     presumably, the ABI code knows where, in the call dummy, the
     return address should be pointed.  */

  /* EMBARCADERO Local: wrapper function must be defined in RTL */
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
	    push sp  */
      gdb_assert (fcw_fcallwrapper_val);
      sp = gdbarch_push_dummy_call (gdbarch, fcw_fcallwrapper_val,
				    get_current_regcache (),
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
      /* Push the call args.  This will result in: 
	    push bp_addr
	    push struct_addr (if struct_return)
	    for each arg:
	      push arg
	    push sp  */
      sp = gdbarch_push_dummy_call (gdbarch, function,
				    get_current_regcache (),
				    bp_addr, nargs, args,
				    sp, struct_return, struct_addr);
    }
  do_cleanups (args_cleanup);

  /* Set up a frame ID for the dummy frame so we can pass it to
     set_momentary_breakpoint.  We need to give the breakpoint a frame
     ID so that the breakpoint code can correctly re-identify the
     dummy breakpoint.  */
  /* Sanity.  The exact same SP value is returned by PUSH_DUMMY_CALL,
     saved as the dummy-frame TOS, and used by dummy_id to form
     the frame ID's stack address.  */
  dummy_id = frame_id_build (sp, bp_addr);

  /* Create a momentary breakpoint at the return address of the
     inferior.  That way it breaks when it returns.  */

  {
    struct breakpoint *bpt;
    struct symtab_and_line sal;

    init_sal (&sal);		/* initialize to zeroes */
    sal.pspace = current_program_space;
    sal.pc = bp_addr;
    sal.section = find_pc_overlay (sal.pc);
    /* Sanity.  The exact same SP value is returned by
       PUSH_DUMMY_CALL, saved as the dummy-frame TOS, and used by
       dummy_id to form the frame ID's stack address.  */
    bpt = set_momentary_breakpoint (gdbarch, sal, dummy_id, bp_call_dummy);
    bpt->disposition = disp_del;
  }

  /* Create a breakpoint in std::terminate.
     If a C++ exception is raised in the dummy-frame, and the
     exception handler is (normally, and expected to be) out-of-frame,
     the default C++ handler will (wrongly) be called in an inferior
     function call.  This is wrong, as an exception can be  normally
     and legally handled out-of-frame.  The confines of the dummy frame
     prevent the unwinder from finding the correct handler (or any
     handler, unless it is in-frame).  The default handler calls
     std::terminate.  This will kill the inferior.  Assert that
     terminate should never be called in an inferior function
     call.  Place a momentary breakpoint in the std::terminate function
     and if triggered in the call, rewind.  */
  if (unwind_on_terminating_exception_p)
    set_std_terminate_breakpoint ();

  /* Everything's ready, push all the info needed to restore the
     caller (and identify the dummy-frame) onto the dummy-frame
     stack.  */
  dummy_frame_push (caller_state, &dummy_id);

  /* Discard both inf_status and caller_state cleanups.
     From this point on we explicitly restore the associated state
     or discard it.  */
  discard_cleanups (inf_status_cleanup);

  /* Register a clean-up for unwind_on_terminating_exception_breakpoint.  */
  terminate_bp_cleanup = make_cleanup (cleanup_delete_std_terminate_breakpoint,
				       NULL);

  /* - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP - SNIP -
     If you're looking to implement asynchronous dummy-frames, then
     just below is the place to chop this function in two..  */

  /* TP is invalid after run_inferior_call returns, so enclose this
     in a block so that it's only in scope during the time it's valid.  */
  {
    struct thread_info *tp = inferior_thread ();

    /* Save this thread's ptid, we need it later but the thread
       may have exited.  */
    call_thread_ptid = tp->ptid;

    /* Run the inferior until it stops.  */

    e = run_inferior_call (tp, real_pc);
  }

  /* Rethrow an error if we got one trying to run the inferior.  */

  if (e.reason < 0)
    {
      const char *name = get_function_name (funaddr,
                                            name_buf, sizeof (name_buf));

      discard_infcall_control_state (inf_status);

      /* We could discard the dummy frame here if the program exited,
         but it will get garbage collected the next time the program is
         run anyway.  */

      switch (e.reason)
	{
	case RETURN_ERROR:
	  throw_error (e.error, _("%s\n\
An error occurred while in a function called from GDB.\n\
Evaluation of the expression containing the function\n\
(%s) will be abandoned.\n\
When the function is done executing, GDB will silently stop."),
		       e.message, name);
	case RETURN_QUIT:
	default:
	  throw_exception (e);
	}
    }

  /* If the program has exited, or we stopped at a different thread,
     exit and inform the user.  */

  if (! target_has_execution)
    {
      const char *name = get_function_name (funaddr,
					    name_buf, sizeof (name_buf));

      /* If we try to restore the inferior status,
	 we'll crash as the inferior is no longer running.  */
      discard_infcall_control_state (inf_status);

      /* We could discard the dummy frame here given that the program exited,
         but it will get garbage collected the next time the program is
         run anyway.  */

      error (_("The program being debugged exited while in a function "
	       "called from GDB.\n"
	       "Evaluation of the expression containing the function\n"
	       "(%s) will be abandoned."),
	     name);
    }

  if (! ptid_equal (call_thread_ptid, inferior_ptid))
    {
      const char *name = get_function_name (funaddr,
					    name_buf, sizeof (name_buf));

      /* We've switched threads.  This can happen if another thread gets a
	 signal or breakpoint while our thread was running.
	 There's no point in restoring the inferior status,
	 we're in a different thread.  */
      discard_infcall_control_state (inf_status);
      /* Keep the dummy frame record, if the user switches back to the
	 thread with the hand-call, we'll need it.  */
      if (stopped_by_random_signal)
	error (_("\
The program received a signal in another thread while\n\
making a function call from GDB.\n\
Evaluation of the expression containing the function\n\
(%s) will be abandoned.\n\
When the function is done executing, GDB will silently stop."),
	       name);
      else
	error (_("\
The program stopped in another thread while making a function call from GDB.\n\
Evaluation of the expression containing the function\n\
(%s) will be abandoned.\n\
When the function is done executing, GDB will silently stop."),
	       name);
    }

  if (stopped_by_random_signal || stop_stack_dummy != STOP_STACK_DUMMY)
    {
      const char *name = get_function_name (funaddr,
					    name_buf, sizeof (name_buf));

      if (stopped_by_random_signal)
	{
	  /* We stopped inside the FUNCTION because of a random
	     signal.  Further execution of the FUNCTION is not
	     allowed.  */

	  if (unwind_on_signal_p)
	    {
	      /* The user wants the context restored.  */

	      /* We must get back to the frame we were before the
		 dummy call.  */
	      dummy_frame_pop (dummy_id);

	      /* We also need to restore inferior status to that before the
		 dummy call.  */
	      restore_infcall_control_state (inf_status);

	      /* FIXME: Insert a bunch of wrap_here; name can be very
		 long if it's a C++ name with arguments and stuff.  */
	      error (_("\
The program being debugged was signaled while in a function called from GDB.\n\
GDB has restored the context to what it was before the call.\n\
To change this behavior use \"set unwindonsignal off\".\n\
Evaluation of the expression containing the function\n\
(%s) will be abandoned."),
		     name);
	    }
	  else
	    {
	      /* The user wants to stay in the frame where we stopped
		 (default).
		 Discard inferior status, we're not at the same point
		 we started at.  */
	      discard_infcall_control_state (inf_status);

	      /* FIXME: Insert a bunch of wrap_here; name can be very
		 long if it's a C++ name with arguments and stuff.  */
	      error (_("\
The program being debugged was signaled while in a function called from GDB.\n\
GDB remains in the frame where the signal was received.\n\
To change this behavior use \"set unwindonsignal on\".\n\
Evaluation of the expression containing the function\n\
(%s) will be abandoned.\n\
When the function is done executing, GDB will silently stop."),
		     name);
	    }
	}

      if (stop_stack_dummy == STOP_STD_TERMINATE)
	{
	  /* We must get back to the frame we were before the dummy
	     call.  */
	  dummy_frame_pop (dummy_id);

	  /* We also need to restore inferior status to that before
	     the dummy call.  */
	  restore_infcall_control_state (inf_status);

	  error (_("\
The program being debugged entered a std::terminate call, most likely\n\
caused by an unhandled C++ exception.  GDB blocked this call in order\n\
to prevent the program from being terminated, and has restored the\n\
context to its original state before the call.\n\
To change this behaviour use \"set unwind-on-terminating-exception off\".\n\
Evaluation of the expression containing the function (%s)\n\
will be abandoned."),
		 name);
	}
      else if (stop_stack_dummy == STOP_NONE)
	{

	  /* We hit a breakpoint inside the FUNCTION.
	     Keep the dummy frame, the user may want to examine its state.
	     Discard inferior status, we're not at the same point
	     we started at.  */
	  discard_infcall_control_state (inf_status);

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
Evaluation of the expression containing the function\n\
(%s) will be abandoned.\n\
When the function is done executing, GDB will silently stop."),
		 name);
	}

      /* The above code errors out, so ...  */
      internal_error (__FILE__, __LINE__, _("... should not be here"));
    }

  do_cleanups (terminate_bp_cleanup);

  /* If we get here the called FUNCTION ran to completion,
     and the dummy frame has already been popped.  */

  {
    struct address_space *aspace = get_regcache_aspace (stop_registers);
    struct regcache *retbuf = regcache_xmalloc (gdbarch, aspace);
    struct cleanup *retbuf_cleanup = make_cleanup_regcache_xfree (retbuf);
    struct value *retval = NULL;

    regcache_cpy_no_passthrough (retbuf, stop_registers);

    /* Inferior call is successful.  Restore the inferior status.
       At this stage, leave the RETBUF alone.  */
    restore_infcall_control_state (inf_status);

    /* EMBARCADERO Local: begin fCall Wrapper */
    /* Handle the case that an exception was caught by the function call
       wrapper.  */
    if (fcw_exception_raised ())
      {
	const char *name = get_function_name (funaddr,
					      name_buf, sizeof (name_buf));
	error (_("\
An exception was raised during the evaluation of an expression involving \
a call to function (%s).  The exception was caught by the Delphi runtime \
and the context was restored."), name);
      }
    /* EMBARCADERO Local: end fCall Wrapper */

    /* Figure out the value returned by the function.  */
    retval = allocate_value (values_type);

    /* EMBARCADERO Local: Delphi struct return */
    if (current_language->la_language != language_pascal
        && lang_struct_return)
      read_value_memory (retval, 0, 1, struct_addr,
			 value_contents_raw (retval),
			 TYPE_LENGTH (values_type));
    else if (TYPE_CODE (target_values_type) != TYPE_CODE_VOID)
      {
	/* If the function returns void, don't bother fetching the
	   return value.  */
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
	    /* EMBARCADERO Local begin: Delphi struct return */
	    if (current_language->la_language == language_pascal)
	      {
		VALUE_LVAL (retval) = lval_memory;
		set_value_address (retval, struct_addr);
		set_value_lazy (retval, 1);
	      }
	    else
	    /* EMBARCADERO Local end: Delphi struct return */
	      {
	        read_value_memory (retval, 0, 1, struct_addr,
			           value_contents_raw (retval),
			           TYPE_LENGTH (values_type));
	      }
	    break;
          }
      }

    do_cleanups (retbuf_cleanup);

    /* EMBARCADERO LOCAL: do not forget cleanup FCW in case of nested calls */
    do_cleanups(fcw_cleanup);
    gdb_assert (retval);
    return retval;
  }
}


/* Provide a prototype to silence -Wmissing-prototypes.  */
void _initialize_infcall (void);

void
_initialize_infcall (void)
{
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

  add_setshow_boolean_cmd ("unwind-on-terminating-exception", no_class,
			   &unwind_on_terminating_exception_p, _("\
Set unwinding of stack if std::terminate is called while in call dummy."), _("\
Show unwinding of stack if std::terminate() is called while in a call dummy."),
			   _("\
The unwind on terminating exception flag lets the user determine\n\
what gdb should do if a std::terminate() call is made from the\n\
default exception handler.  If set, gdb unwinds the stack and restores\n\
the context to what it was before the call.  If unset, gdb allows the\n\
std::terminate call to proceed.\n\
The default is to unwind the frame."),
			   NULL,
			   show_unwind_on_terminating_exception_p,
			   &setlist, &showlist);

}
