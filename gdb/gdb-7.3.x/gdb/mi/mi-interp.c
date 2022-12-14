/* MI Interpreter Definitions and Commands for GDB, the GNU debugger.

   Copyright (C) 2002, 2003, 2004, 2005, 2007, 2008, 2009, 2010, 2011
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

#include "defs.h"
#include <unistd.h>
#include "gdb_string.h"
#include "interps.h"
#include "event-top.h"
#include "event-loop.h"
#include "inferior.h"
#include "ui-out.h"
#include "top.h"
#include "exceptions.h"
#include "mi-main.h"
#include "mi-cmds.h"
#include "mi-out.h"
#include "mi-console.h"
#include "mi-common.h"
#include "observer.h"
#include "gdbthread.h"
#include "solist.h"

/* These are the interpreter setup, etc. functions for the MI interpreter */
static void mi_execute_command_wrapper (char *cmd);
static void mi_command_loop (int mi_version);

/* These are hooks that we put in place while doing interpreter_exec
   so we can report interesting things that happened "behind the mi's
   back" in this command */
static int mi_interp_query_hook (const char *ctlstr, va_list ap)
     ATTRIBUTE_PRINTF (1, 0);

static void mi3_command_loop (void);
static void mi2_command_loop (void);
static void mi1_command_loop (void);

static void mi_insert_notify_hooks (void);
static void mi_remove_notify_hooks (void);
static void mi_on_normal_stop (struct bpstats *bs, int print_frame);

static void mi_new_thread (struct thread_info *t);
static void mi_thread_exit (struct thread_info *t, int silent);
static void mi_inferior_added (struct inferior *inf);
static void mi_inferior_appeared (struct inferior *inf);
static void mi_inferior_exit (struct inferior *inf);
static void mi_inferior_removed (struct inferior *inf);
static void mi_on_resume (ptid_t ptid);
static void mi_solib_loaded (struct so_list *solib);
static void mi_solib_unloaded (struct so_list *solib);
static void mi_about_to_proceed (void);

static int report_initial_inferior (struct inferior *inf, void *closure);

static void *
mi_interpreter_init (int top_level)
{
  struct mi_interp *mi = XMALLOC (struct mi_interp);

  /* HACK: We need to force stdout/stderr to point at the console.  This avoids
     any potential side effects caused by legacy code that is still
     using the TUI / fputs_unfiltered_hook.  So we set up output channels for
     this now, and swap them in when we are run. */

  raw_stdout = stdio_fileopen (stdout);

  /* Create MI channels */
  mi->out = mi_console_file_new (raw_stdout, "~", '"');
  mi->err = mi_console_file_new (raw_stdout, "&", '"');
  mi->log = mi->err;
  mi->targ = mi_console_file_new (raw_stdout, "@", '"');
  mi->event_channel = mi_console_file_new (raw_stdout, "=", 0);

 if (getenv("MIGDB_DEBUG") != NULL)
  {
    char logname[64];
    sprintf ( logname, "migdb_%d.log", getpid() );
    file_log_fs = fopen(logname, "a+");
    if (NULL == file_log_fs)
      perror ("Can't open MI logfile:");
    else
      file_log = stdio_fileopen (file_log_fs);
  }

  if (top_level)
    {
      observer_attach_new_thread (mi_new_thread);
      observer_attach_thread_exit (mi_thread_exit);
      observer_attach_inferior_added (mi_inferior_added);
      observer_attach_inferior_appeared (mi_inferior_appeared);
      observer_attach_inferior_exit (mi_inferior_exit);
      observer_attach_inferior_removed (mi_inferior_removed);
      observer_attach_normal_stop (mi_on_normal_stop);
      observer_attach_target_resumed (mi_on_resume);
      observer_attach_solib_loaded (mi_solib_loaded);
      observer_attach_solib_unloaded (mi_solib_unloaded);
      observer_attach_about_to_proceed (mi_about_to_proceed);

      /* The initial inferior is created before this function is called, so we
	 need to report it explicitly.  Use iteration in case future version
	 of GDB creates more than one inferior up-front.  */
      iterate_over_inferiors (report_initial_inferior, mi);
    }

  return mi;
}

static int
mi_interpreter_resume (void *data)
{
  struct mi_interp *mi = data;

  /* As per hack note in mi_interpreter_init, swap in the output channels... */
  gdb_setup_readline ();

  /* These overwrite some of the initialization done in
     _intialize_event_loop.  */
  call_readline = gdb_readline2;
  input_handler = mi_execute_command_wrapper;
  add_file_handler (input_fd, stdin_event_handler, 0);
  async_command_editing_p = 0;
  /* FIXME: This is a total hack for now.  PB's use of the MI
     implicitly relies on a bug in the async support which allows
     asynchronous commands to leak through the commmand loop.  The bug
     involves (but is not limited to) the fact that sync_execution was
     erroneously initialized to 0.  Duplicate by initializing it thus
     here...  */
  sync_execution = 0;

  gdb_stdout = mi->out;
  /* Route error and log output through the MI */
  gdb_stderr = mi->err;
  gdb_stdlog = mi->log;
  /* Route target output through the MI. */
  gdb_stdtarg = mi->targ;
  /* Route target error through the MI as well. */
  gdb_stdtargerr = mi->targ;

  /* Replace all the hooks that we know about.  There really needs to
     be a better way of doing this... */
  clear_interpreter_hooks ();

  deprecated_show_load_progress = mi_load_progress;

  /* If we're _the_ interpreter, take control. */
  if (current_interp_named_p (INTERP_MI1))
    deprecated_command_loop_hook = mi1_command_loop;
  else if (current_interp_named_p (INTERP_MI2))
    deprecated_command_loop_hook = mi2_command_loop;
  else if (current_interp_named_p (INTERP_MI3))
    deprecated_command_loop_hook = mi3_command_loop;
  else
    deprecated_command_loop_hook = mi2_command_loop;

  return 1;
}

static int
mi_interpreter_suspend (void *data)
{
  gdb_disable_readline ();
  return 1;
}

static struct gdb_exception
mi_interpreter_exec (void *data, const char *command)
{
  char *tmp = alloca (strlen (command) + 1);

  strcpy (tmp, command);
  mi_execute_command_wrapper (tmp);
  return exception_none;
}

/* Never display the default gdb prompt in mi case.  */
static int
mi_interpreter_prompt_p (void *data)
{
  return 0;
}

void
mi_cmd_interpreter_exec (char *command, char **argv, int argc)
{
  struct interp *interp_to_use;
  int i;
  char *mi_error_message = NULL;
  struct cleanup *old_chain;

  if (argc < 2)
    error (_("-interpreter-exec: "
	     "Usage: -interpreter-exec interp command"));

  interp_to_use = interp_lookup (argv[0]);
  if (interp_to_use == NULL)
    error (_("-interpreter-exec: could not find interpreter \"%s\""),
	   argv[0]);

  if (!interp_exec_p (interp_to_use))
    error (_("-interpreter-exec: interpreter \"%s\" "
	     "does not support command execution"),
	      argv[0]);

  /* Insert the MI out hooks, making sure to also call the interpreter's hooks
     if it has any. */
  /* KRS: We shouldn't need this... Events should be installed and they should
     just ALWAYS fire something out down the MI channel... */
  mi_insert_notify_hooks ();

  /* Now run the code... */

  old_chain = make_cleanup (null_cleanup, 0);
  for (i = 1; i < argc; i++)
    {
      struct gdb_exception e = interp_exec (interp_to_use, argv[i]);

      if (e.reason < 0)
	{
	  mi_error_message = xstrdup (e.message);
	  make_cleanup (xfree, mi_error_message);
	  break;
	}
    }

  mi_remove_notify_hooks ();

  if (mi_error_message != NULL)
    error ("%s", mi_error_message);
  do_cleanups (old_chain);
}

/*
 * mi_insert_notify_hooks - This inserts a number of hooks that are
 * meant to produce async-notify ("=") MI messages while running
 * commands in another interpreter using mi_interpreter_exec.  The
 * canonical use for this is to allow access to the gdb CLI
 * interpreter from within the MI, while still producing MI style
 * output when actions in the CLI command change gdb's state.
*/

static void
mi_insert_notify_hooks (void)
{
  deprecated_query_hook = mi_interp_query_hook;
}

static void
mi_remove_notify_hooks (void)
{
  deprecated_query_hook = NULL;
}

static int
mi_interp_query_hook (const char *ctlstr, va_list ap)
{
  return 1;
}

static void
mi_execute_command_wrapper (char *cmd)
{
  mi_execute_command (cmd, stdin == instream);
}

static void
mi1_command_loop (void)
{
  mi_command_loop (1);
}

static void
mi2_command_loop (void)
{
  mi_command_loop (2);
}

static void
mi3_command_loop (void)
{
  mi_command_loop (3);
}

static void
mi_command_loop (int mi_version)
{
  /* Turn off 8 bit strings in quoted output.  Any character with the
     high bit set is printed using C's octal format. */
  sevenbit_strings = 1;
  /* Tell the world that we're alive */
  fputs_unfiltered ("(gdb) \n", raw_stdout);
  gdb_flush (raw_stdout);
  /* Log to file.  */
  if (file_log)
    {
      fputs_unfiltered ("(gdb) \n", file_log);
      gdb_flush (file_log);
    }
  start_event_loop ();
}

static void
mi_new_thread (struct thread_info *t)
{
  struct mi_interp *mi = top_level_interpreter_data ();
  struct inferior *inf = find_inferior_pid (ptid_get_pid (t->ptid));

  gdb_assert (inf);

  fprintf_unfiltered (mi->event_channel, 
		      "thread-created,id=\"%d\",group-id=\"i%d\"",
		      t->num, inf->num);
  gdb_flush (mi->event_channel);
  /* Log to file.  */	
  if (file_log)
    {
      fprintf_unfiltered (file_log, 
		          "thread-created,id=\"%d\",group-id=\"i%d\"",
		          t->num, inf->num);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_thread_exit (struct thread_info *t, int silent)
{
  struct mi_interp *mi;
  struct inferior *inf;

  if (silent)
    return;

  inf = find_inferior_pid (ptid_get_pid (t->ptid));

  mi = top_level_interpreter_data ();
  target_terminal_ours ();
  fprintf_unfiltered (mi->event_channel, 
		      "thread-exited,id=\"%d\",group-id=\"i%d\"",
		      t->num, inf->num);
  gdb_flush (mi->event_channel);
  /* Log to file.  */	
  if (file_log)
    {
      fprintf_unfiltered (file_log, 
		          "thread-exited,id=\"%d\",group-id=\"i%d\"",
		          t->num, inf->num);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_inferior_added (struct inferior *inf)
{
  struct mi_interp *mi = top_level_interpreter_data ();

  target_terminal_ours ();
  fprintf_unfiltered (mi->event_channel,
		      "thread-group-added,id=\"i%d\"",
		      inf->num);
  gdb_flush (mi->event_channel);
  /* Log to file.  */
  if (file_log)
    {
      fprintf_unfiltered (file_log,
		          "thread-group-added,id=\"i%d\"",
		          inf->num);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

CORE_ADDR text_low_addr, text_high_addr;

static void
find_text_section_lowhigh_addrs (bfd *abfd, 
				 asection *asect, 
			         void *arg)
{
  const char *name = bfd_section_name (abfd, asect);

  if (!strcmp (".text", name))
    {
      text_low_addr = bfd_section_vma (abfd, asect);
      text_high_addr = text_low_addr + bfd_section_size (abfd, asect);
    }
}


static void
mi_inferior_appeared (struct inferior *inf)
{
  struct mi_interp *mi = top_level_interpreter_data ();

  target_terminal_ours ();
  fprintf_unfiltered (mi->event_channel,
		      "thread-group-started,id=\"i%d\",pid=\"%d\"",
		      inf->num, inf->pid);
  gdb_flush (mi->event_channel);

  /* Log to file.  */	
  if (file_log)
    {
      fprintf_unfiltered (file_log,
		          "thread-group-started,id=\"i%d\",pid=\"%d\"",
		          inf->num, inf->pid);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }

  /* EMBARCADERO LOCAL: Inform IDE about main executable text section addr range 
     as faked library loaded notification */
  if (inf->pspace->ebfd &&
      !is_target_linux_android())
    {
      /* Locate .text section for main exe for getting its low and high addresses */
      bfd_map_over_sections (inf->pspace->ebfd, find_text_section_lowhigh_addrs, NULL);

      char *addr_low_str = paddress(get_current_arch (), text_low_addr);
      char *addr_high_str = paddress(get_current_arch (), text_high_addr);
 
      fprintf_unfiltered (mi->event_channel,
			  "library-loaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\",symbols-loaded=\"%d\","
			  "addr-low=\"%s\",addr-high=\"%s\"",
			  bfd_get_filename (inf->pspace->ebfd), bfd_get_filename (inf->pspace->ebfd),
			  bfd_get_filename (inf->pspace->ebfd), 1, 
			  addr_low_str, addr_high_str);
      gdb_flush (mi->event_channel);

      /* Log to file.  */	
      if (file_log) 
        {
          fprintf_unfiltered (file_log,
			  "library-loaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\",symbols-loaded=\"%d\","
			  "addr-low=\"%s\",addr-high=\"%s\"",
			  bfd_get_filename (inf->pspace->ebfd), bfd_get_filename (inf->pspace->ebfd),
			  bfd_get_filename (inf->pspace->ebfd), 1, 
			  addr_low_str, addr_high_str);
          gdb_flush (file_log);
        }
    }
}

static void
mi_inferior_exit (struct inferior *inf)
{
  struct mi_interp *mi = top_level_interpreter_data ();

  target_terminal_ours ();
  if (inf->has_exit_code)
    {
      fprintf_unfiltered (mi->event_channel,
			  "thread-group-exited,id=\"i%d\",exit-code=\"%s\"",
			  inf->num, int_string (inf->exit_code, 8, 0, 0, 1));
      /* Log to file.  */	
      if (file_log)
        fprintf_unfiltered (file_log,
			    "thread-group-exited,id=\"i%d\",exit-code=\"%s\"",
			    inf->num, int_string (inf->exit_code, 8, 0, 0, 1));
    }
  else
    {
      fprintf_unfiltered (mi->event_channel,
			  "thread-group-exited,id=\"i%d\"", inf->num);
      /* Log to file.  */
      if (file_log)
        fprintf_unfiltered (file_log,
			    "thread-group-exited,id=\"i%d\"", inf->num);
    }

  gdb_flush (mi->event_channel);  
  /* Log to file.  */	
  if (file_log)
    {
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_inferior_removed (struct inferior *inf)
{
  struct mi_interp *mi = top_level_interpreter_data ();

  target_terminal_ours ();
  fprintf_unfiltered (mi->event_channel,
		      "thread-group-removed,id=\"i%d\"",
		      inf->num);
  gdb_flush (mi->event_channel);
  /* Log to file.  */	
  if (file_log)
    {
      fprintf_unfiltered (file_log,
		          "thread-group-removed,id=\"i%d\"",
		          inf->num);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_on_normal_stop (struct bpstats *bs, int print_frame)
{
  /* Since this can be called when CLI command is executing,
     using cli interpreter, be sure to use MI uiout for output,
     not the current one.  */
  struct ui_out *mi_uiout = interp_ui_out (top_level_interpreter ());

  if (print_frame)
    {
      int core;

      if (uiout != mi_uiout)
	{
	  /* The normal_stop function has printed frame information into 
	     CLI uiout, or some other non-MI uiout.  There's no way we
	     can extract proper fields from random uiout object, so we print
	     the frame again.  In practice, this can only happen when running
	     a CLI command in MI.  */
	  struct ui_out *saved_uiout = uiout;

	  uiout = mi_uiout;
	  print_stack_frame (get_selected_frame (NULL), 0, SRC_AND_LOC);
	  uiout = saved_uiout;
	}

      ui_out_field_int (mi_uiout, "thread-id",
			pid_to_thread_id (inferior_ptid));
      if (non_stop)
	{
	  struct cleanup *back_to = make_cleanup_ui_out_list_begin_end 
	    (mi_uiout, "stopped-threads");

	  ui_out_field_int (mi_uiout, NULL,
			    pid_to_thread_id (inferior_ptid));
	  do_cleanups (back_to);
	}
      else
	ui_out_field_string (mi_uiout, "stopped-threads", "all");

      core = target_core_of_thread (inferior_ptid);
      if (core != -1)
	ui_out_field_int (mi_uiout, "core", core);
    }
  
  fputs_unfiltered ("*stopped", raw_stdout);
  /* Log to file.  */	
  if (file_log)
    fputs_unfiltered ("*stopped", file_log);
  mi_out_put (mi_uiout, raw_stdout);
  mi_out_rewind (mi_uiout);
  mi_print_timing_maybe ();
  fputs_unfiltered ("\n", raw_stdout);
  gdb_flush (raw_stdout);
  /* Log to file.  */	
  if (file_log)
    {
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_about_to_proceed (void)
{
  /* Suppress output while calling an inferior function.  */

  if (!ptid_equal (inferior_ptid, null_ptid))
    {
      struct thread_info *tp = inferior_thread ();

      if (tp->control.in_infcall)
	return;
    }

  mi_proceeded = 1;
}

static int
mi_output_running_pid (struct thread_info *info, void *arg)
{
  ptid_t *ptid = arg;

  if (ptid_get_pid (*ptid) == ptid_get_pid (info->ptid))
    {
      fprintf_unfiltered (raw_stdout,
			  "*running,thread-id=\"%d\"\n",
			  info->num);
    /* Log to file */	
    if (file_log)
      fprintf_unfiltered (file_log,
			  "*running,thread-id=\"%d\"\n",
			  info->num);
    }
  return 0;
}

static int
mi_inferior_count (struct inferior *inf, void *arg)
{
  if (inf->pid != 0)
    {
      int *count_p = arg;
      (*count_p)++;
    }

  return 0;
}

static void
mi_on_resume (ptid_t ptid)
{
  struct thread_info *tp = NULL;

  if (ptid_equal (ptid, minus_one_ptid) || ptid_is_pid (ptid))
    tp = inferior_thread ();
  else
    tp = find_thread_ptid (ptid);

  /* Suppress output while calling an inferior function.  */
  if (tp->control.in_infcall)
    return;

  /* To cater for older frontends, emit ^running, but do it only once
     per each command.  We do it here, since at this point we know
     that the target was successfully resumed, and in non-async mode,
     we won't return back to MI interpreter code until the target
     is done running, so delaying the output of "^running" until then
     will make it impossible for frontend to know what's going on.

     In future (MI3), we'll be outputting "^done" here.  */
  if (!running_result_record_printed && mi_proceeded)
    {
      fprintf_unfiltered (raw_stdout, "%s^running\n",
			  current_token ? current_token : "");
      /* Log to file */	
      if (file_log)
        fprintf_unfiltered (file_log, "%s^running\n",
			    current_token ? current_token : "");
    }

  if (PIDGET (ptid) == -1)
    {
      fprintf_unfiltered (raw_stdout, "*running,thread-id=\"all\"\n");
      /* Log to file.  */	
      if (file_log)
        fprintf_unfiltered (file_log, "*running,thread-id=\"all\"\n");
    }
  else if (ptid_is_pid (ptid))
    {
      int count = 0;

      /* Backwards compatibility.  If there's only one inferior,
	 output "all", otherwise, output each resumed thread
	 individually.  */
      iterate_over_inferiors (mi_inferior_count, &count);

      if (count == 1)
        {
	  fprintf_unfiltered (raw_stdout, "*running,thread-id=\"all\"\n");
	  /* Log to file.  */	
	  if (file_log)
	    fprintf_unfiltered (file_log, "*running,thread-id=\"all\"\n");
	}
      else
	iterate_over_threads (mi_output_running_pid, &ptid);
    }
  else
    {
      struct thread_info *ti = find_thread_ptid (ptid);

      gdb_assert (ti);
      fprintf_unfiltered (raw_stdout, "*running,thread-id=\"%d\"\n", ti->num);
      /* Log to file.  */	
      if (file_log)
        fprintf_unfiltered (file_log, "*running,thread-id=\"%d\"\n", ti->num);
    }

  if (!running_result_record_printed && mi_proceeded)
    {
      running_result_record_printed = 1;
      /* This is what gdb used to do historically -- printing prompt even if
	 it cannot actually accept any input.  This will be surely removed
	 for MI3, and may be removed even earler.  */
      /* FIXME: review the use of target_is_async_p here -- is that
	 what we want? */
      if (!target_is_async_p ())
        {
	  fputs_unfiltered ("(gdb) \n", raw_stdout);
          /* Log to file.  */	
          if (file_log)
	    fputs_unfiltered ("(gdb) \n", file_log);
        }
    }
  gdb_flush (raw_stdout);
  /* Log to file.  */	
  if (file_log)
    gdb_flush (file_log);
}

static void
mi_solib_loaded (struct so_list *solib)
{
  struct mi_interp *mi = top_level_interpreter_data ();
  char *addr_low_str = paddress(get_current_arch (), solib->addr_low);
  char *addr_high_str = paddress(get_current_arch (), solib->addr_high);

  target_terminal_ours ();
  if (gdbarch_has_global_solist (target_gdbarch))
    {
      fprintf_unfiltered (mi->event_channel,
			  "library-loaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\",symbols-loaded=\"%d\","
			  "addr-low=\"%s\",addr-high=\"%s\"",
			  solib->so_original_name, solib->so_original_name,
			  solib->so_name, solib->symbols_loaded, 
			  addr_low_str, addr_high_str);
      /* Log to file.  */	
      if (file_log)
        fprintf_unfiltered (file_log,
			    "library-loaded,id=\"%s\",target-name=\"%s\","
			    "host-name=\"%s\",symbols-loaded=\"%d\","
			    "addr-low=\"%s\",addr-high=\"%s\"",
			    solib->so_original_name, solib->so_original_name,
			    solib->so_name, solib->symbols_loaded,
			    addr_low_str, addr_high_str);
    }
  else
    {
      fprintf_unfiltered (mi->event_channel,
			  "library-loaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\",symbols-loaded=\"%d\","
			  "addr-low=\"%s\",addr-high=\"%s\","
			  "thread-group=\"i%d\"",
			  solib->so_original_name, solib->so_original_name,
			  solib->so_name, solib->symbols_loaded,
			  addr_low_str, addr_high_str,
			  current_inferior ()->num);
      /* Log to file.  */
      if (file_log)
        fprintf_unfiltered (file_log,
			    "library-loaded,id=\"%s\",target-name=\"%s\","
			    "host-name=\"%s\",symbols-loaded=\"%d\","
			    "addr-low=\"%s\",addr-high=\"%s\","
			    "thread-group=\"i%d\"",
			    solib->so_original_name, solib->so_original_name,
			    solib->so_name, solib->symbols_loaded,
			    addr_low_str, addr_high_str,
			    current_inferior ()->num);
    }

  gdb_flush (mi->event_channel);
  /* Log to file.  */	
  if (file_log)
    {
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static void
mi_solib_unloaded (struct so_list *solib)
{
  struct mi_interp *mi = top_level_interpreter_data ();

  target_terminal_ours ();
  if (gdbarch_has_global_solist (target_gdbarch))
    {
      fprintf_unfiltered (mi->event_channel,
			  "library-unloaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\"",
			  solib->so_original_name, solib->so_original_name,
			  solib->so_name);
      /* Log to file.  */
      if (file_log)
        fprintf_unfiltered (file_log,
			    "library-unloaded,id=\"%s\",target-name=\"%s\","
			    "host-name=\"%s\"",
			    solib->so_original_name, solib->so_original_name,
			    solib->so_name);
    }
  else
    {
      fprintf_unfiltered (mi->event_channel,
			  "library-unloaded,id=\"%s\",target-name=\"%s\","
			  "host-name=\"%s\",thread-group=\"i%d\"",
			  solib->so_original_name, solib->so_original_name,
			  solib->so_name, current_inferior ()->num);
      /* Log to file.  */
      if (file_log)
        fprintf_unfiltered (file_log,
			    "library-unloaded,id=\"%s\",target-name=\"%s\","
			    "host-name=\"%s\",thread-group=\"i%d\"",
			    solib->so_original_name, solib->so_original_name,
			    solib->so_name, current_inferior ()->num);
    }

  gdb_flush (mi->event_channel);
  /* Log to file.  */
  if (file_log)
    {
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
}

static int
report_initial_inferior (struct inferior *inf, void *closure)
{
  /* This function is called from mi_intepreter_init, and since
     mi_inferior_added assumes that inferior is fully initialized
     and top_level_interpreter_data is set, we cannot call
     it here.  */
  struct mi_interp *mi = closure;

  target_terminal_ours ();
  fprintf_unfiltered (mi->event_channel,
		      "thread-group-added,id=\"i%d\"",
		      inf->num);
  gdb_flush (mi->event_channel);
  /* Log to file.  */	
  if (file_log)
    {
      fprintf_unfiltered (file_log,
			  "thread-group-added,id=\"i%d\"",
			  inf->num);
      fputs_unfiltered ("\n", file_log);
      gdb_flush (file_log);
    }
  return 0;
}

extern initialize_file_ftype _initialize_mi_interp; /* -Wmissing-prototypes */

void
_initialize_mi_interp (void)
{
  static const struct interp_procs procs =
  {
    mi_interpreter_init,	/* init_proc */
    mi_interpreter_resume,	/* resume_proc */
    mi_interpreter_suspend,	/* suspend_proc */
    mi_interpreter_exec,	/* exec_proc */
    mi_interpreter_prompt_p	/* prompt_proc_p */
  };

  /* The various interpreter levels.  */
  interp_add (interp_new (INTERP_MI1, NULL, mi_out_new (1), &procs));
  interp_add (interp_new (INTERP_MI2, NULL, mi_out_new (2), &procs));
  interp_add (interp_new (INTERP_MI3, NULL, mi_out_new (3), &procs));

  /* "mi" selects the most recent released version.  "mi2" was
     released as part of GDB 6.0.  */
  interp_add (interp_new (INTERP_MI, NULL, mi_out_new (2), &procs));
}
