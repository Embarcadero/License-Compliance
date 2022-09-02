/* Pascal language support routines for GDB, the GNU debugger.

   Copyright 2000, 2002, 2003, 2004, 2005 Free Software Foundation,
   Inc.

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
   Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.  */

/* This file is derived from c-lang.c */

#include "defs.h"
#include "gdb_string.h"
#include "gdb_assert.h"
#include "symtab.h"
#include "gdbtypes.h"
#include "expression.h"
#include "parser-defs.h"
#include "language.h"
/* EMBARCADERO LOCAL: Delphi UTF support */
#include "c-lang.h"
#include "p-lang.h"
#include "valprint.h"
#include "value.h"
#include "charset.h"
#include "gdb_obstack.h"
#include <ctype.h>
 
extern void _initialize_pascal_language (void);

/* EMBARCADERO LOCAL Delphi main function */
/* The name of the symbol to use to get the name of the main subprogram.  */
static char PASCAL_MAIN_PROGRAM_SYMBOL_NAME[]
  = "_main";

/* EMBARCADERO LOCAL begin Delphi main function */
/* If the main procedure is written in Pascal, then return its name.
   The result is good until the next call.  Return NULL if the main
   procedure doesn't appear to be in Pascal.  */

char *
pascal_main_name (void)
{
  return PASCAL_MAIN_PROGRAM_SYMBOL_NAME;
}
/* EMBARCADERO LOCAL end Delphi main function */

/* Determines if type TYPE is a pascal string type.
   Returns 1 if the type is a known pascal type
   This function is used by p-valprint.c code to allow better string display.
   If it is a pascal string type, then it also sets info needed
   to get the length and the data of the string
   length_pos, length_size and string_pos are given in bytes.
   char_size gives the element size in bytes.
   FIXME: if the position or the size of these fields
   are not multiple of TARGET_CHAR_BIT then the results are wrong
   but this does not happen for Free Pascal nor for GPC.  */
int
is_pascal_string_type (struct type *type,int *length_pos,
                       int *length_size, int *string_pos,
		       struct type **char_type,
		       char **arrayname)
{
  if (TYPE_CODE (type) == TYPE_CODE_STRUCT)
    {
      /* Old Borland type pascal strings from Free Pascal Compiler.  */
      /* Two fields: length and st.  */
      if (TYPE_NFIELDS (type) == 2 
          && TYPE_FIELD_NAME(type, 0)
          && TYPE_FIELD_NAME(type, 1)
          && strcmp (TYPE_FIELDS (type)[0].name, "length") == 0 
          && strcmp (TYPE_FIELDS (type)[1].name, "st") == 0)
        {
          if (length_pos)
	    *length_pos = TYPE_FIELD_BITPOS (type, 0) / TARGET_CHAR_BIT;
          if (length_size)
	    *length_size = TYPE_LENGTH (TYPE_FIELD_TYPE (type, 0));
          if (string_pos)
	    *string_pos = TYPE_FIELD_BITPOS (type, 1) / TARGET_CHAR_BIT;
          if (char_type)
	    *char_type = TYPE_TARGET_TYPE (TYPE_FIELD_TYPE (type, 1));
 	  if (arrayname)
	    *arrayname = TYPE_FIELDS (type)[1].name;
         return 2;
        };
      /* GNU pascal strings.  */
      /* Three fields: Capacity, length and schema$ or _p_schema.  */
      if (TYPE_NFIELDS (type) == 3
          && TYPE_FIELD_NAME(type, 0)
          && TYPE_FIELD_NAME(type, 1)
	  /* KIRILL FIXME: you already test for TYPE_FIELD_NAME(type, 2) below */
          && TYPE_FIELD_NAME(type, 2)
	  /* DAWN FIXME: this is now redundant */
          && TYPE_FIELDS (type)[0].name
          && strcmp (TYPE_FIELDS (type)[0].name, "Capacity") == 0
          && strcmp (TYPE_FIELDS (type)[1].name, "length") == 0)
        {
          if (length_pos)
	    *length_pos = TYPE_FIELD_BITPOS (type, 1) / TARGET_CHAR_BIT;
          if (length_size)
	    *length_size = TYPE_LENGTH (TYPE_FIELD_TYPE (type, 1));
          if (string_pos)
	    *string_pos = TYPE_FIELD_BITPOS (type, 2) / TARGET_CHAR_BIT;
          /* FIXME: how can I detect wide chars in GPC ?? */
          if (char_type)
	    {
	      *char_type = TYPE_TARGET_TYPE (TYPE_FIELD_TYPE (type, 2));
	      if (TYPE_CODE (*char_type) == TYPE_CODE_ARRAY)
		*char_type = TYPE_TARGET_TYPE (*char_type);
	    }
 	  if (arrayname && TYPE_FIELD_NAME(type, 2))
	    *arrayname = TYPE_FIELDS (type)[2].name;
         return 3;
        };
    }
  return 0;
}

/* EMBARCADERO LOCAL: begin Delphi UTF support */
static void pascal_one_char (int, struct type *, struct ui_file *, int *);

/* Print a wide character W to OUTPUT.  ORIG is a pointer to the
   original (target) bytes representing the character, ORIG_LEN is the
   number of valid bytes.  WIDTH is the number of bytes in a base
   characters of the type.  OUTPUT is an obstack to which wide
   characters are emitted.  IN_QUOTES is reset to 0 if a char is
   written with #4 notation.  NEED_ESCAPE is an in/out flag which is
   used to track numeric escapes across calls.  */

static void
pascal_print_wchar (gdb_wint_t w, const gdb_byte *orig, int orig_len,
		    int width, struct obstack *output, int *in_quotes)
{
  if (gdb_iswprint (w))
    {
      gdb_wchar_t wchar = w;

      if (!(*in_quotes))
	obstack_grow_wstr (output, LCST ("'"));
      *in_quotes = 1;

      /* ' becomes ''.  */
      if (w == LCST ('\''))
	obstack_grow_wstr (output, LCST ("''"));
      obstack_grow (output, &wchar, sizeof (gdb_wchar_t));
    }
  else
    {
      int i;

      /* End the string in preparation for #4 notation.  */
      if (*in_quotes)
	obstack_grow_wstr (output, LCST ("'"));
      *in_quotes = 0;

      for (i = 0; i + width <= orig_len; i += width)
	{
	  char octal[30];
	  ULONGEST value = extract_unsigned_integer (&orig[i], width);
	  /* If the value fits in 3 octal digits, print it that
	      way.  Otherwise, print it as a hex escape.  */
	  if (value <= 0777)
	    sprintf (octal, "#%.3o", (int) (value & 0777));
	  else
	    sprintf (octal, "#$%lx", (long) value);
	  append_string_as_wide (octal, output);
	}
      /* If we somehow have extra bytes, print them now.  */
      while (i < orig_len)
	{
	  char octal[5];
	  sprintf (octal, "#%.3o", orig[i] & 0xff);
	  append_string_as_wide (octal, output);
	  ++i;
	}
    }
}
/* EMBARCADERO LOCAL: end Delphi UTF support */

/* Print the character C on STREAM as part of the contents of a literal
   string.
   In_quotes is reset to 0 if a char is written with #4 notation */

/* EMBARCADERO LOCAL: Delphi UTF support */
static void
pascal_one_char (int c, struct type *type, struct ui_file *stream,
		 int *in_quotes)
{
  /* EMBARCADERO LOCAL: begin Delphi UTF support */
  struct obstack wchar_buf, output;
  struct cleanup *cleanups;
  const char *encoding;
  gdb_byte *buf;
  struct wchar_iterator *iter;
  /* EMBARCADERO LOCAL: Delphi UTF support */
  size_t nbytes_in_char;

  classify_type (type, &encoding);

#if 0
  buf = alloca (TYPE_LENGTH (type));
  pack_long (buf, type, c);
#else
  /* EMBARCADERO LOCAL FIXME: It can take multiple UTF chars to complete a
     Unicode char (which can be up to 4 bytes) - we need to account for the
     entire char.  */
  /* EMBARCADERO LOCAL FIXME: Assumes byte order matches host.  */
  nbytes_in_char = get_nbytes_in_wchar (encoding, &c);
  if (nbytes_in_char)
    {
      /* EMBARCADERO LOCAL FIXME: Assumes byte order matches host.  */
      buf = alloca (nbytes_in_char);
      memcpy (&buf[0], &c, nbytes_in_char);
    }
  else
    {
      nbytes_in_char = TYPE_LENGTH (type);
      buf = alloca (nbytes_in_char);
      pack_long (buf, type, c);
    }
#endif

  /* EMBARCADERO LOCAL: Delphi UTF support */
  iter = make_wchar_iterator (buf, nbytes_in_char, encoding,
			      TYPE_LENGTH (type));
  cleanups = make_cleanup_wchar_iterator (iter);

  /* This holds the printable form of the wchar_t data.  */
  obstack_init (&wchar_buf);
  make_cleanup_obstack_free (&wchar_buf);

  while (1)
    {
      int num_chars;
      gdb_wchar_t *chars;
      const gdb_byte *buf;
      size_t buflen;
      int is_printable = 0;
      enum wchar_iterate_result result;

      num_chars = wchar_iterate (iter, &result, &chars, &buf, &buflen);
      if (num_chars < 0)
	break;
      if (num_chars > 0)
	{
	  /* If all characters are printable, print them.  Otherwise,
	     we're going to have to print using #4 notation.  We
	     check all characters because we don't know the character
	     boundaries.  */
	  int i;

	  is_printable = 1;
	  for (i = 0; i < num_chars; ++i)
	    if (!gdb_iswprint (chars[i]))
	      {
		is_printable = 0;
		break;
	      }

	  if (is_printable)
	    {
	      for (i = 0; i < num_chars; ++i)
		pascal_print_wchar (chars[i], buf, buflen, TYPE_LENGTH (type),
				    &wchar_buf, in_quotes);
	    }
	}

      /* This handles the NUM_CHARS == 0 case as well.  */
      if (!is_printable)
	pascal_print_wchar (gdb_WEOF, buf, buflen, TYPE_LENGTH (type), &wchar_buf,
			    in_quotes);
    }
  if (*in_quotes)
    {
      obstack_grow_wstr (&wchar_buf, LCST ("'"));
      *in_quotes = 0;
    }

  /* The output in the host encoding.  */
  obstack_init (&output);
  make_cleanup_obstack_free (&output);

  convert_between_encodings (INTERMEDIATE_ENCODING, host_charset (),
			     obstack_base (&wchar_buf),
			     obstack_object_size (&wchar_buf),
			     1, &output, translit_char);
  obstack_1grow (&output, '\0');

  fputs_filtered (obstack_base (&output), stream);

  do_cleanups (cleanups);
  /* EMBARCADERO LOCAL: end Delphi UTF support */
}

static void pascal_emit_char (int c, struct type *type,
			      struct ui_file *stream, int quoter);

/* Print the character C on STREAM as part of the contents of a literal
   string whose delimiter is QUOTER.  Note that that format for printing
   characters and strings is language specific. */

static void
pascal_emit_char (int c, struct type *type, struct ui_file *stream, int quoter)
{
  int in_quotes = 0;

  /* EMBARCADERO LOCAL: Delphi UTF support */
  pascal_one_char (c, type, stream, &in_quotes);
}

void
pascal_printchar (int c, struct type *type, struct ui_file *stream)
{
  int in_quotes = 0;

  /* EMBARCADERO LOCAL: Delphi UTF support */
  pascal_one_char (c, type, stream, &in_quotes);
}

/* Print the character string STRING, printing at most LENGTH characters.
   Printing stops early if the number hits print_max; repeat counts
   are printed as appropriate.  Print ellipses at the end if we
   had to stop before printing LENGTH characters, or if FORCE_ELLIPSES.  */

void
pascal_printstr (struct ui_file *stream, struct type *type,
		 const gdb_byte *string, unsigned int length,
		 int force_ellipses,
		 const struct value_print_options *options)
{
  unsigned int i;
  unsigned int things_printed = 0;
  int in_quotes = 0;
  int need_comma = 0;
  int width = TYPE_LENGTH (type);
  struct obstack wchar_buf, output;
  struct cleanup *cleanup;
  enum c_string_type str_type;
  const char *encoding;
  struct wchar_iterator *iter;
  int finished = 0;

  /* EMBARCADERO LOCAL: begin Delphi UTF support */
  /* If the string was not truncated due to `set print elements', and
     the last byte of it is a null, we don't print that, in traditional C
     style.  */
  if (!force_ellipses
      && length > 0
      && (extract_unsigned_integer (string + (length - 1) * width, width) == 0))
    length--;

  str_type = classify_type (type, &encoding) & ~C_CHAR;
  (void)str_type;

  if (length == 0)
    {
      fputs_filtered ("''", stream);
      return;
    }

  if (length == -1)
    {
      unsigned long current_char = 1;
      for (i = 0; current_char; ++i)
	{
	  QUIT;
	  current_char = extract_unsigned_integer (string + i * width, width);
	}
      length = i;
    }

  /* Arrange to iterate over the characters, in wchar_t form.  */
  iter = make_wchar_iterator (string, length * width, encoding, width);
  cleanup = make_cleanup_wchar_iterator (iter);

  /* WCHAR_BUF is the obstack we use to represent the string in
     wchar_t form.  */
  obstack_init (&wchar_buf);
  make_cleanup_obstack_free (&wchar_buf);

  while (!finished && things_printed < options->print_max)
    {
      int num_chars;
      enum wchar_iterate_result result;
      gdb_wchar_t *chars;
      const gdb_byte *buf;
      size_t buflen;

      QUIT;

      if (need_comma)
	{
	  obstack_grow_wstr (&wchar_buf, LCST (", "));
	  need_comma = 0;
	}

      num_chars = wchar_iterate (iter, &result, &chars, &buf, &buflen);
      /* We only look at repetitions when we were able to convert a
	 single character in isolation.  This makes the code simpler
	 and probably does the sensible thing in the majority of
	 cases.  */
      while (num_chars == 1 && things_printed < options->print_max)
	{
	  /* Count the number of repetitions.  */
	  unsigned int reps = 0;
	  gdb_wchar_t current_char = chars[0];
	  const gdb_byte *orig_buf = buf;
	  int orig_len = buflen;

	  if (need_comma)
	    {
	      obstack_grow_wstr (&wchar_buf, LCST (", "));
	      need_comma = 0;
	    }

	  while (num_chars == 1 && current_char == chars[0])
	    {
	      num_chars = wchar_iterate (iter, &result, &chars, &buf, &buflen);
	      ++reps;
	    }

	  /* Emit CURRENT_CHAR according to the repetition count and
	     options.  */
	  if (reps > options->repeat_count_threshold)
	    {
	      /* End the previous string.  */
	      if (in_quotes)
		{
		  obstack_grow_wstr (&wchar_buf, LCST ("', "));
		  in_quotes = 0;
		}
	      /* Print the repeated character.  */
	      pascal_print_wchar (current_char, orig_buf, orig_len, width,
				  &wchar_buf, &in_quotes);
	      if (in_quotes)
		{
		  obstack_grow_wstr (&wchar_buf, LCST ("'"));
		  in_quotes = 0;
		}
	      {
		/* Painful gyrations.  */
		int j;
		char *s = xstrprintf (_(" <repeats %u times>"), reps);
		for (j = 0; s[j]; ++j)
		  {
		    gdb_wchar_t w = gdb_btowc (s[j]);
		    obstack_grow (&wchar_buf, &w, sizeof (gdb_wchar_t));
		  }
		xfree (s);
	      }
	      things_printed += options->repeat_count_threshold;
	      need_comma = 1;
	    }
	  else
	    {
	      /* Saw the character one or more times, but fewer than
		 the repetition threshold.  */
	      while (reps-- > 0)
		{
		  pascal_print_wchar (current_char, orig_buf, orig_len, width,
				      &wchar_buf, &in_quotes);
		  ++things_printed;
		}
	    }
	}

      /* NUM_CHARS and the other outputs from wchar_iterate are valid
	 here regardless of which branch was taken above.  */
      if (num_chars < 0)
	{
	  /* Hit EOF.  */
	  finished = 1;
	  break;
	}

      switch (result)
	{
	case wchar_iterate_invalid:
	  pascal_print_wchar (gdb_WEOF, buf, buflen, width, &wchar_buf,
			      &in_quotes);
	  break;

	case wchar_iterate_incomplete:
	  /* End the previous string.  */
	  if (in_quotes)
	    {
	      obstack_grow_wstr (&wchar_buf, LCST ("',"));
	      in_quotes = 0;
	    }
	  obstack_grow_wstr (&wchar_buf, LCST (" <incomplete sequence "));
	  pascal_print_wchar (gdb_WEOF, buf, buflen, width, &wchar_buf,
			      &in_quotes);
	  if (in_quotes)
	    {
	      obstack_grow_wstr (&wchar_buf, LCST ("'"));
	      in_quotes = 0;
	    }
	  obstack_grow_wstr (&wchar_buf, LCST (">"));
	  finished = 1;
	  break;
	}
    }

  /* Terminate the quotes if necessary.  */
  if (in_quotes)
    obstack_grow_wstr (&wchar_buf, LCST ("'"));

  if (force_ellipses || !finished)
    obstack_grow_wstr (&wchar_buf, LCST ("..."));

  /* OUTPUT is where we collect `char's for printing.  */
  obstack_init (&output);
  make_cleanup_obstack_free (&output);

  convert_between_encodings (INTERMEDIATE_ENCODING, host_charset (),
			     obstack_base (&wchar_buf),
			     obstack_object_size (&wchar_buf),
			     1, &output, translit_char);
  obstack_1grow (&output, '\0');

  fputs_filtered (obstack_base (&output), stream);

  do_cleanups (cleanup);
  /* EMBARCADERO LOCAL: end Delphi UTF support */
}

/* EMBARCADERO LOCAL begin Delphi types */
static int
pascal_string_lower_bound (struct gdbarch *current_gdbarch)
{
  /* Default for Pascal is 1.  */
  int lowbound = 1;

  /* Note: the lower bound is 0 for Dcc "nextgen" compilers.  */
  if (current_gdbarch
      && (gdbarch_osabi (current_gdbarch) == GDB_OSABI_DARWINV7
	  || gdbarch_osabi (current_gdbarch) == GDB_OSABI_DARWINV7F
	  || gdbarch_osabi (current_gdbarch) == GDB_OSABI_DARWINV7S
	  || gdbarch_osabi (current_gdbarch) == GDB_OSABI_DARWINV7K))
    lowbound = 0;
  return lowbound;
}

static struct type *
pascal_create_string_type (struct gdbarch *current_gdbarch)
{
  int lowbound;
  struct type *rangetype;
  struct type *stringtype;

  lowbound = pascal_string_lower_bound (current_gdbarch);
  /* Length is unknown until we read the data, so make it 1 for now.  */
  rangetype = create_range_type ((struct type *) NULL,
				  builtin_type_int,
				  lowbound, lowbound + 1);
  stringtype = create_array_type ((struct type *) NULL,
				  builtin_type_Delphi_char,
				  rangetype);
  TYPE_NAME (stringtype) = "string";
  TYPE_CODE (stringtype) = TYPE_CODE_STRING;
  return stringtype;
}

/* Create a fundamental Delphi type using default reasonable for the current
   target machine.

   Some object/debugging file formats (DWARF version 1, COFF, etc) do not
   define fundamental types such as "int" or "double".  Others (stabs or
   DWARF version 2, etc) do define fundamental types.  For the formats which
   don't provide fundamental types, gdb can create such types using this
   function.

   FIXME:  Some compilers distinguish explicitly signed integral types
   (signed short, signed int, signed long) from "regular" integral types
   (short, int, long) in the debugging information.  There is some dis-
   agreement as to how useful this feature is.  In particular, gcc does
   not support this.  Also, only some debugging formats allow the
   distinction to be passed on to a debugger.  For now, we always just
   use "short", "int", or "long" as the type name, for both the implicit
   and explicitly signed types.  This also makes life easier for the
   gdb test suite since we don't have to account for the differences
   in output depending upon what the compiler and debugging format
   support.  We will probably have to re-examine the issue when gdb
   starts taking it's fundamental type information directly from the
   debugging information supplied by the compiler.  fnf@cygnus.com */

struct type *
pascal_create_fundamental_type (struct objfile *objfile, int typeid)
{
  struct type *type = NULL;

  switch (typeid)
    {
    case FT_COMPLEX:
    case FT_DBL_PREC_COMPLEX:
    case FT_EXT_PREC_COMPLEX:
    case FT_FIXED_DECIMAL:
    case FT_FLOAT_DECIMAL:
    case FT_TEMPLATE_ARG:
    default:
      /* FIXME:  For now, if we are asked to produce a type not in this
         language, create the equivalent of a C integer type with the
         name "<?type?>".  When all the dust settles from the type
         reconstruction work, this should probably become an error. */
      type = init_type (TYPE_CODE_INT,
			TARGET_INT_BIT / TARGET_CHAR_BIT,
			0, "<?type?>", objfile);
      warning (_("internal error: no Pascal fundamental type %d"), typeid);
      break;
    case FT_VOID:
      type = init_type (TYPE_CODE_VOID,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			0, "void", objfile);
      break;
    case FT_BOOLEAN:
      type = init_type (TYPE_CODE_BOOL,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "boolean", objfile);
      break;
    case FT_STRING:
      /* FIXME: What's the gdbarch? */
      type = pascal_create_string_type (NULL /*current_gdbarch*/);
      break;
    case FT_BYTE:
      type = init_type (TYPE_CODE_INT,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			0, "shortint", objfile);
      break;
    case FT_UNSIGNED_BYTE:
      type = init_type (TYPE_CODE_INT,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "byte", objfile);
      break;
    case FT_CHAR:
      /* FIXME: Is this supposed to be Delphi char?  */
      type = init_type (TYPE_CODE_CHAR,
			TARGET_SHORT_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "char", objfile);
      break;
    case FT_SIGNED_CHAR:
      type = init_type (TYPE_CODE_INT,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			0, "shortint", objfile);
      break;
    case FT_UNSIGNED_CHAR:
      type = init_type (TYPE_CODE_INT,
			TARGET_CHAR_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "byte", objfile);
      break;
    case FT_SHORT:
      type = init_type (TYPE_CODE_INT,
			TARGET_SHORT_BIT / TARGET_CHAR_BIT,
			0, "smallint", objfile);
      break;
    case FT_SIGNED_SHORT:
      type = init_type (TYPE_CODE_INT,
			TARGET_SHORT_BIT / TARGET_CHAR_BIT,
			0, "smallint", objfile);		/* FIXME-fnf */
      break;
    case FT_UNSIGNED_SHORT:
      type = init_type (TYPE_CODE_INT,
			TARGET_SHORT_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "word", objfile);
      break;
    case FT_INTEGER:
      type = init_type (TYPE_CODE_INT,
			TARGET_INT_BIT / TARGET_CHAR_BIT,
			0, "integer", objfile);
      break;
    case FT_SIGNED_INTEGER:
      type = init_type (TYPE_CODE_INT,
			TARGET_INT_BIT / TARGET_CHAR_BIT,
			0, "integer", objfile);		/* FIXME -fnf */
      break;
    case FT_UNSIGNED_INTEGER:
      type = init_type (TYPE_CODE_INT,
			TARGET_INT_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "cardinal", objfile);
      break;
    case FT_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_BIT / TARGET_CHAR_BIT,
			0, "longint", objfile);
      break;
    case FT_SIGNED_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_BIT / TARGET_CHAR_BIT,
			0, "longint", objfile);	/* FIXME -fnf */
      break;
    case FT_UNSIGNED_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "longword", objfile);
      break;
    case FT_LONG_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_LONG_BIT / TARGET_CHAR_BIT,
			0, "int64", objfile);
      break;
    case FT_SIGNED_LONG_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_LONG_BIT / TARGET_CHAR_BIT,
			0, "int64", objfile);
      break;
    case FT_UNSIGNED_LONG_LONG:
      type = init_type (TYPE_CODE_INT,
			TARGET_LONG_LONG_BIT / TARGET_CHAR_BIT,
			TYPE_FLAG_UNSIGNED, "uint64", objfile);
      break;
    case FT_FLOAT:
      type = init_type (TYPE_CODE_FLT,
			TARGET_FLOAT_BIT / TARGET_CHAR_BIT,
			0, "single", objfile);
      break;
    case FT_DBL_PREC_FLOAT:
      type = init_type (TYPE_CODE_FLT,
			TARGET_DOUBLE_BIT / TARGET_CHAR_BIT,
			0, "double", objfile);
      break;
    case FT_EXT_PREC_FLOAT:
      type = init_type (TYPE_CODE_FLT,
			TARGET_LONG_DOUBLE_BIT / TARGET_CHAR_BIT,
			0, "extended", objfile);
      break;
    }
  return (type);
}


/* Table mapping opcodes into strings for printing operators
   and precedences of the operators.  */

const struct op_print pascal_op_print_tab[] =
{
  {",", BINOP_COMMA, PREC_COMMA, 0},
  {":=", BINOP_ASSIGN, PREC_ASSIGN, 1},
  {"or", BINOP_BITWISE_IOR, PREC_BITWISE_IOR, 0},
  {"xor", BINOP_BITWISE_XOR, PREC_BITWISE_XOR, 0},
  {"and", BINOP_BITWISE_AND, PREC_BITWISE_AND, 0},
  {"=", BINOP_EQUAL, PREC_EQUAL, 0},
  {"<>", BINOP_NOTEQUAL, PREC_EQUAL, 0},
  {"<=", BINOP_LEQ, PREC_ORDER, 0},
  {">=", BINOP_GEQ, PREC_ORDER, 0},
  {">", BINOP_GTR, PREC_ORDER, 0},
  {"<", BINOP_LESS, PREC_ORDER, 0},
  {"shr", BINOP_RSH, PREC_SHIFT, 0},
  {"shl", BINOP_LSH, PREC_SHIFT, 0},
  {"+", BINOP_ADD, PREC_ADD, 0},
  {"-", BINOP_SUB, PREC_ADD, 0},
  {"*", BINOP_MUL, PREC_MUL, 0},
  {"/", BINOP_DIV, PREC_MUL, 0},
  {"div", BINOP_INTDIV, PREC_MUL, 0},
  {"mod", BINOP_REM, PREC_MUL, 0},
  {"@", BINOP_REPEAT, PREC_REPEAT, 0},
  {"-", UNOP_NEG, PREC_PREFIX, 0},
  {"not", UNOP_LOGICAL_NOT, PREC_PREFIX, 0},
  {"^", UNOP_IND, PREC_SUFFIX, 1},
  {"@", UNOP_ADDR, PREC_PREFIX, 0},
  {"sizeof", UNOP_SIZEOF, PREC_PREFIX, 0},
  {NULL, 0, 0, 0}
};

struct type **const (pascal_builtin_types[]) =
{
  &builtin_type_int,
    &builtin_type_long,
    &builtin_type_short,
    &builtin_type_char,
    &builtin_type_float,
    &builtin_type_double,
    &builtin_type_void,
    &builtin_type_long_long,
    &builtin_type_signed_char,
    &builtin_type_unsigned_char,
    &builtin_type_unsigned_short,
    &builtin_type_unsigned_int,
    &builtin_type_unsigned_long,
    &builtin_type_unsigned_long_long,
    &builtin_type_long_double,
    &builtin_type_complex,
    &builtin_type_double_complex,
    /* EMBARCADERO Local Delphi strings */
    &builtin_type_Delphi_char,
    0
};

enum pascal_primitive_types {
  pascal_primitive_type_shortint,
  pascal_primitive_type_byte,
  pascal_primitive_type_boolean,
  pascal_primitive_type_smallint,
  pascal_primitive_type_word,
  pascal_primitive_type_nativeint,
  pascal_primitive_type_nativeuint,
  pascal_primitive_type_longint,
  pascal_primitive_type_integer,
  pascal_primitive_type_longword,
  pascal_primitive_type_cardinal,
  pascal_primitive_type_uint64,
  pascal_primitive_type_int64,
  pascal_primitive_type_single,
  pascal_primitive_type_double,
  pascal_primitive_type_real,
  pascal_primitive_type_extended,
  pascal_primitive_type_void,
  pascal_primitive_type_pointer,
  pascal_primitive_type_char,
  pascal_primitive_type_pchar,
  pascal_primitive_type_string,
  nr_pascal_primitive_types
};

static void
pascal_language_arch_info (struct gdbarch *current_gdbarch,
			   struct language_arch_info *lai)
{
  const struct builtin_type *builtin = builtin_type (current_gdbarch);
  lai->primitive_type_vector
    = GDBARCH_OBSTACK_CALLOC (current_gdbarch, nr_pascal_primitive_types + 1,
			      struct type *);

  lai->primitive_type_vector [pascal_primitive_type_shortint] =
    init_type (TYPE_CODE_INT, TARGET_CHAR_BIT / TARGET_CHAR_BIT,
               0, "shortint", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_byte] =
    init_type (TYPE_CODE_INT, TARGET_CHAR_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
	       "byte", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_boolean] =
    init_type (TYPE_CODE_INT, TARGET_CHAR_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
	       "boolean", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_smallint] =
    init_type (TYPE_CODE_INT, TARGET_SHORT_BIT / TARGET_CHAR_BIT,
	       0, "smallint", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_word] =
    init_type (TYPE_CODE_INT, TARGET_SHORT_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
               "word", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_nativeint] =
    init_type (TYPE_CODE_INT, TARGET_INT_BIT / TARGET_CHAR_BIT,
	       0, "nativeint", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_nativeuint] =
    init_type (TYPE_CODE_INT, TARGET_INT_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
	       "nativeuint", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_longint] =
    init_type (TYPE_CODE_INT, TARGET_LONG_BIT / TARGET_CHAR_BIT,
	       0, "longint", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_integer] =
    init_type (TYPE_CODE_INT, TARGET_LONG_BIT / TARGET_CHAR_BIT,
	       0, "integer", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_longword] =
    init_type (TYPE_CODE_INT, TARGET_LONG_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
               "longword", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_cardinal] =
    init_type (TYPE_CODE_INT, TARGET_LONG_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
               "cardinal", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_uint64] =
    init_type (TYPE_CODE_INT, TARGET_LONG_LONG_BIT / TARGET_CHAR_BIT,
	       0, "uint64", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_int64] =
    init_type (TYPE_CODE_INT, TARGET_LONG_LONG_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
               "int64", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_single] =
    init_type (TYPE_CODE_FLT, TARGET_FLOAT_BIT / TARGET_CHAR_BIT,
               0, "single", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_double] =
    init_type (TYPE_CODE_FLT, TARGET_DOUBLE_BIT / TARGET_CHAR_BIT,
               0, "double", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_real] =
    init_type (TYPE_CODE_FLT, TARGET_DOUBLE_BIT / TARGET_CHAR_BIT,
               0, "real", (struct objfile *) NULL);
  lai->primitive_type_vector [pascal_primitive_type_extended] =
    init_type (TYPE_CODE_FLT, TARGET_LONG_DOUBLE_BIT / TARGET_CHAR_BIT,
               0, "extended", (struct objfile *) NULL);

  lai->primitive_type_vector [pascal_primitive_type_void] = builtin->builtin_void;
  lai->primitive_type_vector [pascal_primitive_type_pointer] =
    lookup_pointer_type (init_type (TYPE_CODE_VOID, 1, 0, "void",
                                    (struct objfile *) NULL));
  TYPE_NAME (lai->primitive_type_vector [pascal_primitive_type_pointer])
    = "pointer";

  /* FIXME: There's no easy way to set the lower bound in the LAI vector as in
       lai->string_lower_bound = pascal_string_lower_bound (current_gdbarch);
     because language functions want to test pointers to see if set.  
     We can't bash the string_lower_bound of the current language either,
     because it is const.  
     The best we can do is assert if things aren't what we expect.  */
  if (current_language->string_lower_bound
	      != pascal_string_lower_bound (current_gdbarch))
    warning (_("internal error: Pascal string lower bound is wrong for this target"));

  /* Note: "char" will map to wchar_t or char16_t depending on target arch,
     but it will always be unsigned short.  */
  lai->string_char_type = 
    lai->primitive_type_vector [pascal_primitive_type_char] =
#if 0
    init_type (TYPE_CODE_CHAR, TARGET_SHORT_BIT / TARGET_CHAR_BIT,
	       TYPE_FLAG_UNSIGNED,
	       "char", (struct objfile *) NULL);
#else
    builtin_type_Delphi_char;
#endif
  lai->primitive_type_vector [pascal_primitive_type_pchar] =
    lookup_pointer_type (lai->string_char_type);
  TYPE_NAME (lai->primitive_type_vector [pascal_primitive_type_pchar])
    = "pchar";

  lai->primitive_type_vector [pascal_primitive_type_string] =
    pascal_create_string_type (current_gdbarch);
}
/* EMBARCADERO LOCAL end Delphi types */

/* The target ABI may pass or return some structs by reference 
   TODO: Add check for additional types may be passed as reference 
   or returned via pointer written by function at struct_addr.
   Delphi class instance result described as pointer to struct target type. */
static int
pascal_pass_by_reference (struct type *type)
{
  if (type != NULL 
      && ((TYPE_CODE(type) == TYPE_CODE_STRUCT)
	  || (TYPE_CODE(type) == TYPE_CODE_UNION)
	  || (TYPE_CODE(type) == TYPE_CODE_PTR
		&& TYPE_TARGET_TYPE (type) != NULL
		&& TYPE_DELPHI_CLASS (TYPE_TARGET_TYPE (type)))
	  || (TYPE_CODE(type) == TYPE_CODE_STRING)))
    return 1;  
  else
    return 0;
}


const struct language_defn pascal_language_defn =
{
  "pascal",			/* Language name */
  language_pascal,
  pascal_builtin_types,
  range_check_on,
  type_check_on,
  /* EMBARCADERO Local: set default for case sensitivity to off */
  case_sensitive_off,
  array_row_major,
  &exp_descriptor_standard,
  pascal_parse,
  pascal_error,
  null_post_parser,
  pascal_printchar,		/* Print a character constant */
  pascal_printstr,		/* Function to print string constant */
  pascal_emit_char,		/* Print a single char */
  pascal_create_fundamental_type,	/* Create fundamental type in this language */
  pascal_print_type,		/* Print a type using appropriate syntax */
  pascal_val_print,		/* Print a value using appropriate syntax */
  pascal_value_print,		/* Print a top-level value */
  NULL,				/* Language specific skip_trampoline */
  value_of_this,		/* value_of_this */
  basic_lookup_symbol_nonlocal,	/* lookup_symbol_nonlocal */
  basic_lookup_transparent_type,/* lookup_transparent_type */
  NULL,				/* Language specific symbol demangler */
  NULL,				/* Language specific class_name_from_physname */
  pascal_op_print_tab,		/* expression operators for printing */
  1,				/* c-style arrays */
  /* EMBARCADERO LOCAL Delphi strings */
  /* FIXME: actual lower bound varies based on target.
     Dcc "nextgen" compilers use lower bound of 0, others use 1.  */
  0,				/* String lower bound */
  &builtin_type_Delphi_char,	/* Type of string elements */
  default_word_break_characters,
  pascal_language_arch_info,
  default_print_array_index,
  pascal_pass_by_reference,
  /* EMBARCADERO LOCAL Delphi strings */
  c_get_string,
  LANG_MAGIC
};

void
_initialize_pascal_language (void)
{
  add_language (&pascal_language_defn);
}
