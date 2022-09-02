/* Perform an inferior function call, for GDB, the GNU debugger.

   Copyright 2003 Free Software Foundation, Inc.

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

#ifndef INFCALL_H
#define INFCALL_H

struct value;
struct type;

extern CORE_ADDR find_function_addr (struct value *function, 
				     struct type **retval_type);

/* Perform a function call in the inferior.

   ARGS is a vector of values of arguments (NARGS of them).  FUNCTION
   is a value, the function to be called.  Returns a value
   representing what the function returned.  May fail to return, if a
   breakpoint or signal is hit during the execution of the function.

   ARGS is modified to contain coerced values. */

extern struct value *call_function_by_hand (struct value *function, int nargs,
					    struct value **args);

/* APPLE LOCAL */
extern int inferior_function_calls_disabled_p;
int set_hand_function_call_timeout (int newval);
int hand_function_call_timeout_p ();

/* EMBARCADERO Local: begin fCall wrapper */
/* Embarcadero fCall wrapper
  
   --- Embarcadero Function Call Wrapper ---

   This technique uses a function call "wrapper" which enables recovery
   form exceptions which might occur during a function call evaluation.  
   The function call "wrapper", named __dbk_fcall_wrapper, is defined in
   the Embarcadero Delphi RTL for use by the debugger, and employs the RTL's
   exception handler to catch user exceptions and unwind from them.
   The RTL code looks something like:

      namespace Sysinit { 
	void __dbkFCallArgs(void* p1, void* p2, ..., p30) { }
      }
      using namespace Sysinit;
      void __dbk_fcall_wrapper()
      {
	void* p;
	__try {
	  __dbkFCallArgs(p, p, ..., p); // BP1 fcw_ReadyToPushPoint
	  // BP2 fcw_ResultFetchPoint
	}
	__except(1) {
	  __dbkFCallArgs(p, p, ..., p); // BP3 fcw_CatchPoint
	}
      }

   Three breakpoints are used by the debugger during the evaluation:

   * fcw_ReadyToPushPoint -
   Breakpoint placed on call to __dbkFCallArgs.  When BP hit, the
   target of the call instruction (__dbkFCallArgs) is replaced by the
   address of the user's function of the intended evaluation, and the
   user's function arguments are placed on the stack and/or in
   registers as appropriate for the ABI.

   * fcw_ResultFetchPoint -
   Breakpoint placed on instruction following the call to __dbkFCallArgs.
   When BP hit, we know the call ended successfully and can collect
   the return value from user registers and/or memory.

   * fcw_CatchPoint -
   Breakpoint placed on 2nd call to __dbkFCallArgs.  In this case, the
   function call is just a marker so the debugger knows where the body
   of the exception handling code begins.  The call itself is left in
   the code as a harmless side effect.  When BP hit, we mark that
   function call failed and save off any exception information that
   might be helpful to the user before resuming so the RTL can finish
   unwinding.  Later, the failure can be reported to the user.

   --- Termonology ---

   The following terminology "shortcuts" are used throughout:
   * fCall - function call
   * fcw - function call wrapper
   * dbk - debugger kernel  

   --- FCW structure globals ---

   The Info needed by the function call wrapper is maintained in a global
   FCW structure CURRENT_FCW with the following fields:
   * fcallwrapper_addr -
     Holds the address of the fCall wrapper function __dbk_fcall_wrapper.
   * fCallCatchTriggered -
     Flag used to tell if an exception was raised during fCall.
   * user_sp -
     User stack for user's function evaluation.
   * user_functionval -
     Value of user's function.
   * user_nargs -
     Number of user args.
   * user_args -
     Array of user arg values.
   * user_struct_return -
     True if user function call involves struct return.
   * user_struct_addr -
     Address of struct return pushed on stack (if user_struct_return).
   * user_real_pc -
     Addr to set PC to when calling user's function.
   * user_lr -
     Addr to set LR to when calling user's function.

   These globals are used in the following:
   - infcall.c (hand_function_call):
       Set real_pc = funaddr (addr of user function)
       Look up fCall wrapper function symbol and if found
	  set fcallwrapper_addr = addr of __dbk_fcall_wrapper
       If fcallwrapper_addr != NULL, then...
	  If real_pc & 0x1,
	      function address is invalid; report error and bail
	  Set user_real_pc = real_pc
	  Set real_pc = fcallwrapper_addr | 1
	  Scan the fCall wrapper at fcallwrapper_addr...
	      Set fcw_ReadyToPushPoint
		  = addr of 1st call to __dbkFCallArgs
	      Set fcw_ResultFetchPoint and user_lr
		  = addr of insn after 1st call to __dbkFCallArgs
		  (the return point of the call)
	      Set fcw_CatchPoint = addr of 2nd call to __dbkFCallArgs
	  Set a temporary BP at fcw_ReadyToPushPoint
	      with name fCallWrapperReadyToArgPush
	  Set a temporary BP at fcw_CatchPoint
	      with name fCallWrapperCatch
	  Set a temporary BP at fcw_ResultFetchPoint
	      with name fCallWrapperGetResult
	  Init fCallCatchTriggered = 0
	  Save values for the "real" user's function call in FCW globals: 
	      set user_functionval = function (user's function)
	      set user_nargs = nargs (user's arg count)
	      set user_args = args (user's function args)
	      set user_struct_return = struct_return
	      set user_struct_addr = struct_addr
	  Set up stack to call __dbk_fcall_wrapper, and pass nargs as 0  
	      with bp_addr = BP addr to set for return of fCall wrapper call,
	      and sp = user's stack (including struct_return, if any),
	      and user's struct_addr (if struct_return)
      Resume the inferior at PC real_pc
      If fCallCatchTriggered != 0 after fCall,
	  report error
   - breakpoint.c (bpstat_what):
      If BP fcw_ReadyToPushPoint hit (has name fCallWrapperReadyToArgPush),
	  push the user's actual args via gdbarch_fcw_argument_push
	  (for ARM, this calls arm_fcw_argument_push)
      If BP fcw_CatchPoint hit (has name fCallWrapperCatch),
	  set fCallCatchTriggered = 1
      If BP fcw_ResultFetchPoint hit (has name fCallWrapperGetResult), and 
	  if fCallCatchTriggered == 0, 
	      save result regs
	      KIRILL FIXME - this code should also save off struct_addr.
   - arm-tdep.c (arm_fcw_argument_push):
      Set LR register to return address in fCall wrapper body:
	  write reg ARM_LR_REGNUM = user_lr | 1
      Set PC register to fCalled function start:
	  write reg ARM_PC_REGNUM = user_real_pc
      If user_nargs && user_args != NULL,
	  user_sp = read reg ARM_SP_REGNUM
      Push user's args via arm_push_actual_fw_args
			     (current_gdbarch, user_functionval,
			      current_regcache, user_nargs,
			      user_args, user_sp,
			      user_struct_return, user_struct_addr)
      If new SP after call == user_sp,
	  return success (else failure).  */

struct fcallwrapper_info
{
  /* Parent structure on stack.  */
  struct fcallwrapper_info *next;

  /* Resolved fCall wrapper function address.  */
  CORE_ADDR fcallwrapper_addr;

  /* Exception raised during fCall flag.  */
  int fCallCatchTriggered;

  /* Temporary BPs at fCall wrapper control points.  */
  struct breakpoint *ReadyToPushPoint_bpt;
  struct breakpoint *CatchPoint_bpt;
  struct breakpoint *ResultFetchPoint_bpt;

  /* Info for user's "real" function call.  */
  struct value *user_functionval;
  int user_nargs;
  struct value **user_args;
  int user_struct_return;
  CORE_ADDR user_struct_addr;
  /* KIRILL FIXME: user_sp is only used locally in arm_fcw_argument_push.
     If that's the only place it's needed, then it should be a local.  
     However, we adjust sp based on whether we push the struct return (if any)
     in hand_function_call, so we may need this as a global afterall.  */
  CORE_ADDR user_sp;
  CORE_ADDR user_real_pc;
  /* KIRILL FIXME: user_lr is ARM specific only, on x86/x64 return addr pushed
     on stack   */
  CORE_ADDR user_lr;
};

/* Return the current function call wrapper info structure.  */
extern struct fcallwrapper_info *get_current_fcw (void);

/* Return 1 if the current function call wrapper is being used (i.e.
   we're in the process of calling a function through the function call
   wrapper).  */
extern int using_current_fcw (void);

/* Push/pop the current fCall wrapper info.  */
extern void push_current_fcw (void);
extern void pop_current_fcw (void);

/* Record/test if the function call wrapper caught an exception thrown by
   the user's function.  */
extern void set_fcw_exception_raised (void);
extern int fcw_exception_raised (void);

/* Test if the function call wrapper control BP was hit.  */
extern int fcw_breakpoint_hit (struct breakpoint *bpt, const char *bp_name);

/* Function for arch independent FCW argument pusher wrapper.
   Returns 1 on success, 0 on error.  */
extern int fcw_argument_push (void);
/* EMBARCADERO Local: end fCall wrapper */

#endif
