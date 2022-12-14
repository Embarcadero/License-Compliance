/* C language support definitions for GDB, the GNU debugger.

   Copyright 1992, 1994, 1995, 1996, 1997, 1998, 2000, 2002, 2005 Free
   Software Foundation, Inc.

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


#if !defined (C_LANG_H)
#define C_LANG_H 1

struct ui_file;
struct language_arch_info;

#include "value.h"
#include "macroexp.h"


/* The various kinds of C string and character.  Note that these
   values are chosen so that they may be or'd together in certain
   ways.  */
enum c_string_type
  {
    /* An ordinary string: "value".  */
    C_STRING = 0,
    /* A wide string: L"value".  */
    C_WIDE_STRING = 1,
    /* A 16-bit Unicode string: u"value".  */
    C_STRING_16 = 2,
    /* A 32-bit Unicode string: U"value".  */
    C_STRING_32 = 3,
    /* An ordinary char: 'v'.  This can also be or'd with one of the
       above to form the corresponding CHAR value from a STRING
       value.  */
    C_CHAR = 4,
    /* A wide char: L'v'.  */
    C_WIDE_CHAR = 5,
    /* A 16-bit Unicode char: u'v'.  */
    C_CHAR_16 = 6,
    /* A 32-bit Unicode char: U'v'.  */
    C_CHAR_32 = 7
  };

/* Defined in c-exp.y.  */

extern int c_parse (void);

extern void c_error (char *);

extern int c_parse_escape (char **, struct obstack *);

/* Defined in c-typeprint.c */
extern void c_print_type (struct type *, char *, struct ui_file *, int,
			  int);

extern int c_val_print (struct type *, const gdb_byte *, int, CORE_ADDR,
			struct ui_file *, int,
			const struct value_print_options *);

extern int c_value_print (struct value *, struct ui_file *,
			  const struct value_print_options *);

/* These are in c-lang.c: */

extern void c_printchar (int, struct type *, struct ui_file *);

extern void c_printstr (struct ui_file * stream, struct type *elttype,
			const gdb_byte *string, unsigned int length,
			int force_ellipses,
			const struct value_print_options *options);

extern void scan_macro_expansion (char *expansion);
extern int scanning_macro_expansion (void);
extern void finished_macro_expansion (void);

extern macro_lookup_ftype *expression_macro_lookup_func;
extern void *expression_macro_lookup_baton;

extern struct type *c_create_fundamental_type (struct objfile *, int);

extern void c_language_arch_info (struct gdbarch *gdbarch,
				  struct language_arch_info *lai);

/* EMBARCADERO LOCAL: begin Delphi UTF support */
extern enum c_string_type classify_type (struct type *elttype, const char **encoding);
extern void append_string_as_wide (const char *string, struct obstack *output);
/* EMBARCADERO LOCAL: end Delphi UTF support */

/* These are in c-typeprint.c: */

extern void c_type_print_base (struct type *, struct ui_file *, int, int);

/* These are in cp-valprint.c */

extern void cp_print_class_member (const gdb_byte *, struct type *,
				   struct ui_file *, char *);

extern void cp_print_value_fields (struct type *, struct type *,
				   const gdb_byte *, int, CORE_ADDR,
				   struct ui_file *, int,
				   const struct value_print_options *,
				   struct type **, int);

extern int cp_is_vtbl_ptr_type (struct type *);

extern int cp_is_vtbl_member (struct type *);

/* These are in c-valprint.c.  */

extern int c_textual_element_type (struct type *, char);


#endif /* !defined (C_LANG_H) */
