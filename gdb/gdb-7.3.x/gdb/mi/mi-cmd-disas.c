/* MI Command Set - disassemble commands.
   Copyright (C) 2000, 2001, 2002, 2007, 2008, 2009, 2010, 2011
   Free Software Foundation, Inc.
   Contributed by Cygnus Solutions (a Red Hat company).

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
#include "arch-utils.h"
#include "target.h"
#include "value.h"
#include "mi-cmds.h"
#include "mi-getopt.h"
#include "gdb_string.h"
#include "ui-out.h"
#include "disasm.h"

#define LOOK_AROUND_RANGE 0x100

/* The arguments to be passed on the command line and parsed here are:
   
   -s START-ADDRESS | -s START-ADDRESS -e END-ADDRESS | -f FILENAME -n
    LINENUM [-n HOW-MANY] [-p PREV-INSTRUCTIONS] [-P PEEK-LIMIT] --
    MIXED-MODE

   START-ADDRESS: address to start the disassembly at.
   END-ADDRESS: address to end the disassembly at.

   or:
   
   START-ADDRESS: address to start the disassembly at.

   or:

   FILENAME: The name of the file where we want disassemble from.
   LINE: The line around which we want to disassemble. It will
   disassemble the function that contins that line.

   In the latter two cases, the '-n HOW-MANY' and '-p
   PREV-INSTRUCTIONS' options can be used to specify the range of
   instructions to display around FILENAME:LINE or START-ADDRESS.  If
   HOW-MANY is not specified, it will disassemble the entire function
   around FILENAME:LINE or START-ADDRESS.  In mixed mode, HOW-MANY
   counts the number of disassembly lines only, not the source lines.

   PREV-INSTRUCTIONS may not be specified without START-ADDRESS.

   On some systems, it is impossible to parse the instruction streams
   backwards from a given instruction.  In those cases, we use
   find_pc_offset to seek backwards, using a known previous
   instruction in the program and aprsing from there.  In such cases,
   the '-P PEEK-LIMIT' option can be used to set a limit on how many
   instructions backwards GDB will search.

   The MIXED-MODE arguemnt is always required.  Zero means disassembly
   only; 1 means mixed source and disassembly, respectively. 
*/

static void
mi_cmd_disassemble_usage (const char *message)
{
  const char *const usage = 
    "[-P peeklimit]"
    " ("
    " [-f filename -l linenum [-n howmany] [-p startprev]]"
    " | [-s startaddr [-n howmany] [-p startprev]]"
    " | [-s startaddr -e endaddr]"
    " )"
    " [--] mixed_mode.";

  error ("mi_cmd_disassemble: %s  Usage: %s", message, usage);
}

void
mi_cmd_disassemble (char *command, char **argv, int argc)
{
  struct symtab *s;
  int mode, disasm_flags;

  /* Which options have we processed ... */
  int file_seen = 0;
  int line_seen = 0;
  int start_seen = 0;
  int end_seen = 0;
  int num_seen = 0;
  int prev_seen = 0;
  int peeklimit_seen = 0;

  /* ... and their corresponding value. */
  char *file_string = NULL;
  int line_num = -1;
  int how_many = -1;
  CORE_ADDR low = 0;
  CORE_ADDR high = 0;
  CORE_ADDR start = 0;
  int prev = 0;
  int peeklimit = -1;

  /* Options processing stuff. */
  int optind = 0;
  char *optarg;
  enum opt
  {
    FILE_OPT, LINE_OPT, NUM_OPT, START_OPT, END_OPT, PREV_OPT, PEEKLIMIT_OPT
  };
  static struct mi_opt opts[] = {
    {"f", FILE_OPT, 1},
    {"l", LINE_OPT, 1},
    {"n", NUM_OPT, 1},
    {"s", START_OPT, 1},
    {"e", END_OPT, 1},
    {"p", PREV_OPT, 1},
    {"P", PEEKLIMIT_OPT, 1},
    {0}
  };

  struct gdbarch *gdbarch = get_current_arch ();
  struct cleanup *cleanups = make_cleanup (null_cleanup, NULL);

  /* Get the options with their arguments. Keep track of what we
     encountered. */
  while (1)
    {
      int opt = mi_getopt ("mi_cmd_disassemble", argc, argv, opts,
			   &optind, &optarg);
      if (opt < 0)
	break;
      switch ((enum opt) opt)
	{
	case FILE_OPT:
	  file_string = xstrdup (optarg);
	  file_seen = 1;
	  break;
	case LINE_OPT:
	  line_num = atoi (optarg);
	  line_seen = 1;
	  break;
	case NUM_OPT:
	  how_many = atoi (optarg);
	  num_seen = 1;
	  break;
	case START_OPT:
	  start = parse_and_eval_address (optarg);
	  start_seen = 1;
	  break;
	case END_OPT:
	  high = parse_and_eval_address (optarg);
	  end_seen = 1;
	  break;
	case PREV_OPT:
	  prev = atoi (optarg);
	  prev_seen = 1;
	  break;
	case PEEKLIMIT_OPT:
	  peeklimit = atoi (optarg);
	  peeklimit_seen = 1;
	  break;
	}
    }
  argv += optind;
  argc -= optind;

  if (argc < 1)
    mi_cmd_disassemble_usage ("Must specify mixed mode argument.");
  if (argc > 1)
    mi_cmd_disassemble_usage ("Extra arguments present.");

  if ((argv[0][0] == '\0') || (argv[0][1] != '\0'))
    mi_cmd_disassemble_usage ("Mixed mode argument must be 0 or 1.");
  if ((argv[0][0] != '0') && (argv[0][0] != '1'))
    mi_cmd_disassemble_usage ("Mixed mode argument must be 0 or 1.");

  mode = atoi (argv[0]);
  if (mode < 0 || mode > 3)
    error (_("-data-disassemble: Mode argument must be 0, 1, 2, or 3."));

  /* Convert the mode into a set of disassembly flags */

  disasm_flags = 0;
  if (mode & 0x1)
    disasm_flags |= DISASSEMBLY_SOURCE;
  if (mode & 0x2)
    disasm_flags |= DISASSEMBLY_RAW_INSN;


  if (start_seen && line_seen)
    mi_cmd_disassemble_usage ("May not specify both a line number and a start address.");

  if ((line_seen && !file_seen) || (file_seen && !line_seen))
    mi_cmd_disassemble_usage ("File and line number must be specified together.");

  if (line_seen && file_seen)
    {
      s = lookup_symtab (file_string);
      if (s == NULL)
	error ("mi_cmd_disassemble: Invalid filename.");
      if (! find_line_pc (s, line_num, &start))
	error ("mi_cmd_disassemble: Invalid line number.");
    }
  else if (! start_seen)
    mi_cmd_disassemble_usage ("No starting point specified.");
  
  if (end_seen)
    {
      if (num_seen || prev_seen)
	mi_cmd_disassemble_usage ("May not specify both an ending address and -n or -p.");

      gdb_disassembly (gdbarch, uiout, file_string, disasm_flags, how_many, start, high);
      return;
    }

  if (find_pc_partial_function (start, NULL, &low, &high) == 0)
    {
      /* If no sym info - even minsyms not available for start address, disassemble 
	 first bytes enough for looking around. */
      warning ("mi_cmd_disassemble: No function contains the specified address.");
      gdb_disassembly (gdbarch, uiout, file_string, disasm_flags, how_many,
						start, start+LOOK_AROUND_RANGE);
      return;
    }
  
  if (! num_seen)
    {
      /* If only the start address is given, disassemble the entire
	 function around the start address.  */
      
      gdb_disassembly (gdbarch, uiout, file_string, disasm_flags, how_many, low, high);
    }

  /* And finally, now we know start_seen, !line_seen, !file_seen, !end_seen, and num_seen. */
  
  if (prev_seen)
    {
      CORE_ADDR tmp;
      int ret;

      ret = find_pc_offset (gdbarch, start, &tmp, -prev, 1, peeklimit);
      if (tmp != INVALID_ADDRESS)
	start = tmp;
    }

  gdb_disassembly (gdbarch, uiout, file_string, disasm_flags, how_many, start, high);

  do_cleanups (cleanups);
}
