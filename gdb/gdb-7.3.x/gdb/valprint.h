/* Declarations for value printing routines for GDB, the GNU debugger.

   Copyright (C) 1986, 1988, 1989, 1991, 1992, 1993, 1994, 2000, 2005, 2007,
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

#ifndef VALPRINT_H
#define VALPRINT_H

/* This is used to pass formatting options to various value-printing
   functions.  */
struct value_print_options
{
  /* Pretty-printing control.  */
  enum val_prettyprint pretty;

  /* Controls pretty printing of arrays.  */
  int prettyprint_arrays;

  /* Controls pretty printing of structures.  */
  int prettyprint_structs;

  /* Controls printing of virtual tables.  */
  int vtblprint;

  /* Controls printing of nested unions.  */
  int unionprint;

  /* Controls printing of addresses.  */
  int addressprint;

  /* Controls looking up an object's derived type using what we find
     in its vtables.  */
  int objectprint;

  /* Maximum number of chars to print for a string pointer value or vector
     contents, or UINT_MAX for no limit.  Note that "set print elements 0"
     stores UINT_MAX in print_max, which displays in a show command as
     "unlimited".  */
  unsigned int print_max;

  /* Print repeat counts if there are more than this many repetitions
     of an element in an array.  */
  unsigned int repeat_count_threshold;

  /* The global output format letter.  */
  int output_format;

  /* The current format letter.  This is set locally for a given call,
     e.g. when the user passes a format to "print".  */
  int format;

  /* Stop printing at null character?  */
  int stop_print_at_null;

  /* True if this value is being printed in an epoch window.  */
  int inspect_it;

  /* True if we should print the index of each element when printing
     an array.  */
  int print_array_indexes;

  /* If nonzero, then dereference references, otherwise just print
     them like pointers.  */
  int deref_ref;

  /* If nonzero, print static fields.  */
  int static_field_print;

  /* If nonzero, print static fields for Pascal.  FIXME: C++ and Java
     share one flag, why not Pascal too?  */
  int pascal_static_field_print;

  /* Controls Python pretty-printing.  */
  int raw;

  /* If nonzero, print the value in "summary" form.  */
  int summary;

  /* EMBARCADERO LOCAL: skip field names */
  /* Controls printing of structure field names.  */
  int field_name_print;

  /* EMBARCADERO LOCAL: expand aggregates in MI */
  /* If nonzero, causes aggregates to be expanded when MI commands are used.  */
  int expand_aggregates;
};

/* The global print options set by the user.  In general this should
   not be directly accessed, except by set/show commands.  Ordinary
   code should call get_user_print_options instead.  */
extern struct value_print_options user_print_options;

/* Initialize *OPTS to be a copy of the user print options.  */
extern void get_user_print_options (struct value_print_options *opts);

/* Initialize *OPTS to be a copy of the user print options, but with
   pretty-printing disabled.  */
extern void get_raw_print_options (struct value_print_options *opts);

/* Initialize *OPTS to be a copy of the user print options, but using
   FORMAT as the formatting option.  */
extern void get_formatted_print_options (struct value_print_options *opts,
					 char format);

extern void maybe_print_array_index (struct type *index_type, LONGEST index,
                                     struct ui_file *stream,
				     const struct value_print_options *);

extern void val_print_array_elements (struct type *, const gdb_byte *, int,
				      CORE_ADDR, struct ui_file *, int,
				      const struct value *,
				      const struct value_print_options *,
				      unsigned int);

extern void val_print_type_code_int (struct type *, const gdb_byte *,
				     struct ui_file *);

extern void val_print_type_code_flags (struct type *type,
				       const gdb_byte *valaddr,
				       struct ui_file *stream);

extern void val_print_scalar_formatted (struct type *,
					const gdb_byte *, int,
					const struct value *,
					const struct value_print_options *,
					int,
					struct ui_file *);

extern void print_binary_chars (struct ui_file *, const gdb_byte *,
				unsigned int, enum bfd_endian);

extern void print_octal_chars (struct ui_file *, const gdb_byte *,
			       unsigned int, enum bfd_endian);

extern void print_decimal_chars (struct ui_file *, const gdb_byte *,
				 unsigned int, enum bfd_endian);

extern void print_hex_chars (struct ui_file *, const gdb_byte *,
			     unsigned int, enum bfd_endian);

extern void print_char_chars (struct ui_file *, struct type *,
			      const gdb_byte *, unsigned int, enum bfd_endian);

int read_string (CORE_ADDR addr, int len, int width, unsigned int fetchlimit,
		 enum bfd_endian byte_order, gdb_byte **buffer,
		 int *bytes_read);

extern void val_print_optimized_out (struct ui_file *stream);

extern void val_print_unavailable (struct ui_file *stream);

extern void val_print_invalid_address (struct ui_file *stream);

#endif
