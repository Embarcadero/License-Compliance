/* Support for printing C values for GDB, the GNU debugger.

   Copyright 1986, 1988, 1989, 1991, 1992, 1993, 1994, 1995, 1996,
   1997, 1998, 1999, 2000, 2001, 2003, 2005 Free Software Foundation,
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
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

#include "defs.h"
#include "gdb_string.h"
#include "symtab.h"
#include "gdbtypes.h"
#include "expression.h"
#include "value.h"
#include "valprint.h"
#include "language.h"
#include "c-lang.h"
#include "cp-abi.h"
#include "target.h"


/* Print function pointer with inferior address ADDRESS onto stdio
   stream STREAM.  */

static void
print_function_pointer_address (CORE_ADDR address, struct ui_file *stream,
				int addressprint)
{
  CORE_ADDR func_addr = gdbarch_convert_from_func_ptr_addr (current_gdbarch,
							    address,
							    &current_target);

  /* If the function pointer is represented by a description, print the
     address of the description.  */
  if (addressprint && func_addr != address)
    {
      fputs_filtered ("@", stream);
      deprecated_print_address_numeric (address, 1, stream);
      fputs_filtered (": ", stream);
    }
  print_address_demangle (func_addr, stream, demangle);
}


/* A helper for c_textual_element_type.  This checks the name of the
   typedef.  This is bogus but it isn't apparent that the compiler
   provides us the help we may need.  */

static int
textual_name (const char *name)
{
  return (!strcmp (name, "wchar_t")
	  || !strcmp (name, "char16_t")
	  || !strcmp (name, "char32_t"));
}

/* Apply a heuristic to decide whether an array of TYPE or a pointer
   to TYPE should be printed as a textual string.  Return non-zero if
   it should, or zero if it should be treated as an array of integers
   or pointer to integers.  FORMAT is the current format letter,
   or 0 if none.

   We guess that "char" is a character.  Explicitly signed and
   unsigned character types are also characters.  Integer data from
   vector types is not.  The user can override this by using the /s
   format letter.  */

int
c_textual_element_type (struct type *type, char format)
{
  struct type *true_type, *iter_type;

  if (format != 0 && format != 's')
    return 0;

  /* We also rely on this for its side effect of setting up all the
     typedef pointers.  */
  true_type = check_typedef (type);

  /* TYPE_CODE_CHAR is always textual.  */
  if (TYPE_CODE (true_type) == TYPE_CODE_CHAR)
    return 1;

  /* Any other character-like types must be integral.  */
  if (TYPE_CODE (true_type) != TYPE_CODE_INT)
    return 0;

  /* We peel typedefs one by one, looking for a match.  */
  iter_type = type;
  while (iter_type)
    {
      /* Check the name of the type.  */
      if (TYPE_NAME (iter_type) && textual_name (TYPE_NAME (iter_type)))
	return 1;

      if (TYPE_CODE (iter_type) != TYPE_CODE_TYPEDEF)
	break;

      /* Peel a single typedef.  If the typedef doesn't have a target
	 type, we use check_typedef and hope the result is ok -- it
	 might be for C++, where wchar_t is a built-in type.  */
      if (TYPE_TARGET_TYPE (iter_type))
	iter_type = TYPE_TARGET_TYPE (iter_type);
      else
	iter_type = check_typedef (iter_type);
    }

  if (format == 's')
    {
      /* Print this as a string if we can manage it.  For now, no
	 wide character support.  */
      if (TYPE_CODE (true_type) == TYPE_CODE_INT
	  && TYPE_LENGTH (true_type) == 1)
	return 1;
    }
  else
    {
      /* If a one-byte TYPE_CODE_INT is missing the not-a-character
	 flag, then we treat it as text; otherwise, we assume it's
	 being used as data.  */
      if (TYPE_CODE (true_type) == TYPE_CODE_INT
	  && TYPE_LENGTH (true_type) == 1
	  && !TYPE_NOTTEXT (true_type))
	return 1;
      /* EMBARCADERO LOCAL begin Delphi char support */
      if (TYPE_CODE (true_type) == TYPE_CODE_INT
	  && TYPE_LENGTH (true_type) == 2
	  && TYPE_NAME (true_type) != NULL
	  && strcmp (TYPE_NAME (true_type), "char16_t") == 0)
	return 1;
      /* EMBARCADERO LOCAL end Delphi char support */
    }

  return 0;
}


/* Print data of type TYPE located at VALADDR (within GDB), which came from
   the inferior at address ADDRESS, onto stdio stream STREAM according to
   OPTIONS.  The data at VALADDR is in target byte order.

   If the data are a string pointer, returns the number of string characters
   printed.  */

int
c_val_print (struct type *type, const gdb_byte *valaddr, int embedded_offset,
	     CORE_ADDR address, struct ui_file *stream, int recurse,
	     const struct value_print_options *options)
{
  unsigned int i = 0;	/* Number of characters printed */
  unsigned len;
  struct type *elttype, *unresolved_elttype;
  struct type *unresolved_type = type;
  unsigned eltlen;
  LONGEST val;
  CORE_ADDR addr;
  int vector_int8s = 0;
  int vector_floats = 0;

  CHECK_TYPEDEF (type);
  switch (TYPE_CODE (type))
    {
    case TYPE_CODE_ARRAY:
      unresolved_elttype = TYPE_TARGET_TYPE (type);
      elttype = check_typedef (unresolved_elttype);
      if (TYPE_LENGTH (type) > 0 && TYPE_LENGTH (unresolved_elttype) > 0)
	{
	  eltlen = TYPE_LENGTH (elttype);
	  len = TYPE_LENGTH (type) / eltlen;
	  if (options->prettyprint_arrays)
	    {
	      print_spaces_filtered (2 + 2 * recurse, stream);
	    }

          /* APPLE LOCAL: gdb will print the int8_t elements of a vector
             register as a string or as characters -- neither of which is
             what the user expects 99% of the time.  Instead, detect that
             we're looking at a vector's int8_t array and treat it
             specially.  */
          if (eltlen == 1 
              && TYPE_VECTOR (type) 
              && TYPE_CODE (elttype) == TYPE_CODE_INT
              && options->format == 0)
            {
              vector_int8s = 1;
            }

          /* APPLE LOCAL: Detect if we're about to print an array of
             v4_float or v2_doubles in a vector register  */
          if ((eltlen == 4 || eltlen == 8)
              && TYPE_VECTOR (type) 
              && TYPE_CODE (elttype) == TYPE_CODE_FLT)
            {
              vector_floats = 1;
            }

	  /* Print arrays of textual chars with a string syntax.  */
	  if (c_textual_element_type (unresolved_elttype, options->format))
	    {
	      /* If requested, look for the first null char and only print
	         elements up to it.  */
	      if (options->stop_print_at_null)
		{
		  unsigned int temp_len;

		  for (temp_len = 0;
		       (temp_len < len
			&& temp_len < options->print_max + 1
			&& extract_unsigned_integer (valaddr + embedded_offset
						     + temp_len * eltlen,
						     eltlen) == 0);
		       ++temp_len)
		    ;
		  len = temp_len;
		}

	      LA_PRINT_STRING (stream, unresolved_elttype,
			       valaddr + embedded_offset, len, 0, options);
	      i = len;
	    }
	  else
	    {
	      fprintf_filtered (stream, "{");
	      /* If this is a virtual function table, print the 0th
	         entry specially, and the rest of the members normally.  */
	      if (cp_is_vtbl_ptr_type (elttype))
		{
		  i = 1;
		  fprintf_filtered (stream, _("%d vtable entries"), len - 1);
		}
	      else
		{
		  i = 0;
		}
              
#if 0 // EMBARCADERO FIXME: where did this go?
              /* If this is an array of int8_t's in a vector register,
                 force it to print as decimal by default, not as
                 decimal value + octal escaped char.  */
              if (format == 0 && vector_int8s)
                format = 'd';

              /* If this is an array of v4_float or v2_doubles in a vector
                 register, force it to print with the '%a' floating point hex
                 formatter when "p/x" is used.  Default formatter remains the
                 '%g' style.  */
              if (format == 'x' && vector_floats)
                format = 'A';
#endif

	      val_print_array_elements (type, valaddr + embedded_offset, 
                                        address, stream,
                                        recurse, options, i);
	      fprintf_filtered (stream, "}");
	    }
	  break;
	}
      /* Array of unspecified length: treat like pointer to first elt.  */
      addr = address;
      goto print_unpacked_pointer;

    case TYPE_CODE_MEMBERPTR:
      if (options->format)
	{
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  options, 0, stream);
	  break;
	}
      cp_print_class_member (valaddr + embedded_offset,
			     TYPE_DOMAIN_TYPE (type),
			     stream, "&");
      break;

    case TYPE_CODE_METHODPTR:
      cplus_print_method_ptr (valaddr + embedded_offset, type, stream);
      break;

    case TYPE_CODE_PTR:
      if (options->format && options->format != 's')
	{
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  options, 0, stream);
	  break;
	}
      if (options->vtblprint && cp_is_vtbl_ptr_type (type))
	{
	  /* Print the unmangled name if desired.  */
	  /* Print vtable entry - we only get here if we ARE using
	     -fvtable_thunks.  (Otherwise, look under TYPE_CODE_STRUCT.) */
	  CORE_ADDR addr
	    = extract_typed_address (valaddr + embedded_offset, type);
	  print_function_pointer_address (addr, stream, options->addressprint);
	  break;
	}
      unresolved_elttype = TYPE_TARGET_TYPE (type);
      elttype = check_typedef (unresolved_elttype);
	{
	  addr = unpack_pointer (type, valaddr + embedded_offset);
	print_unpacked_pointer:

	  if (TYPE_CODE (elttype) == TYPE_CODE_FUNC)
	    {
	      /* Try to print what function it points to.  */
	      print_function_pointer_address (addr, stream,
					      options->addressprint);
	      /* Return value is irrelevant except for string pointers.  */
	      return (0);
	    }

	  if (options->addressprint)
	    {
	      deprecated_print_address_numeric (addr, 1, stream);
	    }

	  /* For a pointer to a textual type, also print the string
	     pointed to, unless pointer is null.  */

	  if (c_textual_element_type (unresolved_elttype, options->format)
	      && addr != 0)
	    {
	      i = val_print_string (unresolved_elttype, addr, -1, stream,
				    options);
	    }
	  else if (cp_is_vtbl_member (type))
	    {
	      /* print vtbl's nicely */
	      CORE_ADDR vt_address = unpack_pointer (type, valaddr + embedded_offset);

	      struct minimal_symbol *msymbol =
	      lookup_minimal_symbol_by_pc (vt_address);
	      if ((msymbol != NULL) &&
		  (vt_address == SYMBOL_VALUE_ADDRESS (msymbol)))
		{
		  fputs_filtered (" <", stream);
		  fputs_filtered (SYMBOL_PRINT_NAME (msymbol), stream);
		  fputs_filtered (">", stream);
		}
	      if (vt_address && options->vtblprint)
		{
		  struct value *vt_val;
		  struct symbol *wsym = (struct symbol *) NULL;
		  struct type *wtype;
		  struct block *block = (struct block *) NULL;
		  int is_this_fld;

		  if (msymbol != NULL)
		    wsym = lookup_symbol (DEPRECATED_SYMBOL_NAME (msymbol), block,
					  VAR_DOMAIN, &is_this_fld, NULL);

		  if (wsym)
		    {
		      wtype = SYMBOL_TYPE (wsym);
		    }
		  else
		    {
		      wtype = unresolved_elttype;
		    }
		  vt_val = value_at (wtype, vt_address);
		  common_val_print (vt_val, stream, recurse + 1, options,
				    current_language);
		  if (options->pretty)
		    {
		      fprintf_filtered (stream, "\n");
		      print_spaces_filtered (2 + 2 * recurse, stream);
		    }
		}
	    }

	  /* Return number of characters printed, including the terminating
	     '\0' if we reached the end.  val_print_string takes care including
	     the terminating '\0' if necessary.  */
	  return i;
	}
      break;

    case TYPE_CODE_REF:
      elttype = check_typedef (TYPE_TARGET_TYPE (type));
      if (options->addressprint)
	{
	  CORE_ADDR addr
	    = extract_typed_address (valaddr + embedded_offset, type);
	  fprintf_filtered (stream, "@");
	  deprecated_print_address_numeric (addr, 1, stream);
	  if (options->deref_ref)
	    fputs_filtered (": ", stream);
	}
      /* De-reference the reference.  */
      if (options->deref_ref)
	{
	  if (TYPE_CODE (elttype) != TYPE_CODE_UNDEF)
	    {
	      struct value *deref_val =
	      value_at
	      (TYPE_TARGET_TYPE (type),
	       unpack_pointer (lookup_pointer_type (builtin_type_void),
			       valaddr + embedded_offset));
	      common_val_print (deref_val, stream, recurse, options,
				current_language);
	    }
	  else
	    fputs_filtered ("???", stream);
	}
      break;

    case TYPE_CODE_UNION:
      if (recurse && !options->unionprint)
	{
	  fprintf_filtered (stream, "{...}");
	  break;
	}
      /* Fall through.  */
    case TYPE_CODE_STRUCT:
      /*FIXME: Abstract this away */
      if (options->vtblprint && cp_is_vtbl_ptr_type (type))
	{
	  /* Print the unmangled name if desired.  */
	  /* Print vtable entry - we only get here if NOT using
	     -fvtable_thunks.  (Otherwise, look under TYPE_CODE_PTR.) */
	  int offset = (embedded_offset +
			TYPE_FIELD_BITPOS (type, VTBL_FNADDR_OFFSET) / 8);
	  struct type *field_type = TYPE_FIELD_TYPE (type, VTBL_FNADDR_OFFSET);
	  CORE_ADDR addr
	    = extract_typed_address (valaddr + offset, field_type);

	  print_function_pointer_address (addr, stream, options->addressprint);
	}
      /* EMBARCADERO LOCAL begin Delphi strings.  */
      else if (TYPE_NAME (type)
	      && (!strcmp (TYPE_NAME (type), "System::UnicodeString"))
	      && TYPE_NFIELDS (type) == 1)
	{
	  struct value *deref_val;

	  elttype = check_typedef (TYPE_FIELD_TYPE (type, 0));
	  if (TYPE_CODE (elttype) != TYPE_CODE_PTR)
	    goto not_a_Delphi_string;
	  /* Figure out the type of the characters.  */
	  elttype = TYPE_TARGET_TYPE (elttype);
	  elttype = check_typedef (elttype);
	  eltlen = TYPE_LENGTH (elttype);
	  len = TYPE_LENGTH (type) / eltlen;
	  if (options->prettyprint_arrays)
	    {
	      print_spaces_filtered (2 + 2 * recurse, stream);
	    }
	  /* For an array of chars, print with string syntax.  */
	  /* EMBARCADERO LOCAL Delphi strings.  */
	  if (c_textual_element_type (elttype, options->format))
	    {
	      int errcode;			/* Error from last read. */
	      CORE_ADDR stringaddr = 0;
	      unsigned int stringlength = 0;
	      unsigned int stringcharwidth = 0;
	      int force_ellipsis = 0;	/* Force ellipsis to be printed if nonzero. */

	      /* Extract the address.  */
	      stringaddr
		= unpack_pointer (lookup_pointer_type (builtin_type_void),
				  valaddr + embedded_offset);
	      if (0 != stringaddr)
		{
		  /* The string length is 4 bytes before the string.  */
		  errcode = target_read_memory (stringaddr - 4, (gdb_byte*)&stringlength, 4);
		  if (errcode == 0)
		    {
		      if (stringlength >= options->print_max)
			{
			  stringlength = options->print_max;
			  force_ellipsis = 1;
			}
		      /* The char size is 10 bytes before the string.  */
		      errcode = target_read_memory (stringaddr - 10, (gdb_byte*)&stringcharwidth, 2);
		    }
		    /* Got all bytes of string pointer from target and length,
		       can print now */
		    if ((errcode == 0) && stringcharwidth && stringlength
			&& (stringcharwidth <= 2))
		      {
			void *buffer;

			buffer = xmalloc (stringlength * stringcharwidth);
			/* Read the string.  */
			errcode = target_read_memory (stringaddr, buffer,
						      stringlength * stringcharwidth);
			if (errcode == 0)
			  {
			    LA_PRINT_STRING (stream, elttype, buffer, stringlength,
					     force_ellipsis, options);
			    i = stringlength;
			  }
			else
			  {
			    if (errcode == EIO)
			      {
				fprintf_filtered (stream, " <Address ");
				fputs_filtered (paddress (stringaddr), stream);
				fprintf_filtered (stream, " out of bounds>");
			      }
			    else
			      {
				fprintf_filtered (stream, " <Error reading address ");
				fputs_filtered (paddress (stringaddr), stream);
				fprintf_filtered (stream, ": %s>", safe_strerror (errcode));
			      }
			  }
			xfree (buffer);
		      }
		    else
		      {
			/* String is empty */
			i = 0;
			fprintf_filtered (stream, "''");
		      }
		}
	      else
		{
		  i = 0;
		  /* String is nil */
		  fprintf_filtered (stream, "''");
		}
	      gdb_flush (stream);
	    }
	  break;
	}
      else
      /* EMBARCADERO LOCAL end Delphi strings.  */
      not_a_Delphi_string:
	/* EMBARCADERO LOCAL begin delphireturn structs */
	/* delphireturn structs with 1 field are empty wrappers around the
	   real Delphi type.  Strip off the empty wrapper when displaying
	   these types.  */
	if (TYPE_DELPHI_RETURN (type)
	    && TYPE_NFIELDS (type) == 1)
	  {
	    if (TYPE_N_BASECLASSES (type) == 1)
	      type = TYPE_BASECLASS (type, 0);
	    else
	      type = TYPE_FIELD_TYPE (type, 0);
	    return c_val_print (type, valaddr, embedded_offset,
				address, stream, recurse, options);
	  }
	/* EMBARCADERO LOCAL end delphireturn structs */
	cp_print_value_fields (type, type, valaddr, embedded_offset, address,
			       stream, recurse, options, NULL, 0);
      break;

    case TYPE_CODE_ENUM:
      if (options->format)
	{
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  options, 0, stream);
	  break;
	}
      len = TYPE_NFIELDS (type);
      val = unpack_long (type, valaddr + embedded_offset);
      for (i = 0; i < len; i++)
	{
	  QUIT;
	  if (val == TYPE_FIELD_BITPOS (type, i))
	    {
	      break;
	    }
	}
      if (i < len)
	{
	  fputs_filtered (TYPE_FIELD_NAME (type, i), stream);
	}
      else
	{
	  print_longest (stream, 'd', 0, val);
	}
      break;

    case TYPE_CODE_FLAGS:
      if (options->format)
	  print_scalar_formatted (valaddr + embedded_offset, type, options, 0, stream);
      else
	val_print_type_code_flags (type, valaddr + embedded_offset, stream);
      break;

    case TYPE_CODE_FUNC:
    case TYPE_CODE_METHOD:
      if (options->format)
	{
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  options, 0, stream);
	  break;
	}
      /* FIXME, we should consider, at least for ANSI C language, eliminating
         the distinction made between FUNCs and POINTERs to FUNCs.  */
      fprintf_filtered (stream, "{");
      type_print (type, "", stream, -1);
      fprintf_filtered (stream, "} ");
      /* Try to print what function it points to, and its address.  */
      print_address_demangle (address, stream, demangle);
      break;

    case TYPE_CODE_BOOL:
      if (options->format || options->output_format)
	{
	  struct value_print_options opts = *options;
	  opts.format = (options->format ? options->format
			 : options->output_format);
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  &opts, 0, stream);
	}
      else
	{
	  val = unpack_long (type, valaddr + embedded_offset);
	  if (val == 0)
	    fputs_filtered ("false", stream);
	  else if (val == 1)
	    fputs_filtered ("true", stream);
	  else
	    print_longest (stream, 'd', 0, val);
	}
      break;

    case TYPE_CODE_RANGE:
      /* FIXME: create_range_type does not set the unsigned bit in a
         range type (I think it probably should copy it from the target
         type), so we won't print values which are too large to
         fit in a signed integer correctly.  */
      /* FIXME: Doesn't handle ranges of enums correctly.  (Can't just
         print with the target type, though, because the size of our type
         and the target type might differ).  */
      /* FALLTHROUGH */

    case TYPE_CODE_INT:
      /* EMBARCADERO LOCAL: begin support of decimal scale for System::Currency type */ 
      if (TYPE_DECIMAL_SCALE (type))
	{
	  double d;
	  char scale;
          void *buffer = NULL;
	  char *bufptr;

	  /* Fetch as 64-bit integer, then cast to double */
	  d = (double)*((int64_t*)(valaddr + embedded_offset));
	  scale = TYPE_DECIMAL_SCALE (type);

	  for (; scale > 0; --scale)
	    d *= 10;

	  for (; scale < 0; ++scale)
	    d /= 10;

	  /* Strip trailing zeroes if required - dirty but effective...*/
	  buffer = xmalloc (64); //allocate enough space
	  if (NULL != buffer)
	    {
	      memset (buffer, '0', 64);
	      sprintf((char*)buffer, "%6.4f" , d);
	      bufptr = (char*)((char*)buffer + strlen((char*)buffer) - 1);
	      while ((bufptr > (char*)buffer)
		      && (( *bufptr == '0' ) || ( *bufptr == '.' )))
		{
		  if (*bufptr == '.')
		    {
		      *bufptr = 0;
		      break;
		    }
		  else								
		    *bufptr-- = 0;
		}
	      fprintf_filtered (stream, "%s", (char*)buffer);
	    }
	  else
	    {
	      fprintf_filtered (stream, "%6.4f", d);
	    }
	  if (NULL != buffer)
	    xfree (buffer);
	}
      /* EMBARCADERO LOCAL: end support of decimal scale for System::Currency type */ 
      else if (options->format || options->output_format)
	{
	  struct value_print_options opts = *options;
	  opts.format = (options->format ? options->format
			 : options->output_format);
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  &opts, 0, stream);
	}
      else
	{
	  val_print_type_code_int (type, valaddr + embedded_offset, stream);
	  /* C and C++ has no single byte int type, char is used instead.
	     Since we don't know whether the value is really intended to
	     be used as an integer or a character, print the character
	     equivalent as well.  */
	  if (c_textual_element_type (unresolved_type, options->format))
	    {
	      fputs_filtered (" ", stream);
	      LA_PRINT_CHAR (unpack_long (type, valaddr + embedded_offset),
			     unresolved_type, stream);
	    }
	}
      break;

    case TYPE_CODE_CHAR:
      if (options->format || options->output_format)
	{
	  struct value_print_options opts = *options;
	  opts.format = (options->format ? options->format
			 : options->output_format);
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  &opts, 0, stream);
	}
      else
	{
	  val = unpack_long (type, valaddr + embedded_offset);
	  if (TYPE_UNSIGNED (type))
	    fprintf_filtered (stream, "%u", (unsigned int) val);
	  else
	    fprintf_filtered (stream, "%d", (int) val);
	  fputs_filtered (" ", stream);
	  LA_PRINT_CHAR ((unsigned char) val, unresolved_type, stream);
	}
      break;

    case TYPE_CODE_FLT:
      if (options->format)
	{
	  print_scalar_formatted (valaddr + embedded_offset, type,
				  options, 0, stream);
	}
      else
	{
	  print_floating (valaddr + embedded_offset, type, stream);
	}
      break;

    case TYPE_CODE_VOID:
      fprintf_filtered (stream, "void");
      break;

    case TYPE_CODE_ERROR:
      /* APPLE LOCAL display error as unknown type */
      fprintf_filtered (stream, _("<unknown type>"));
      break;

    case TYPE_CODE_UNDEF:
      /* This happens (without TYPE_FLAG_STUB set) on systems which don't use
         dbx xrefs (NO_DBX_XREFS in gcc) if a file has a "struct foo *bar"
         and no complete type for struct foo in that file.  */
      fprintf_filtered (stream, _("<incomplete type>"));
      break;

    case TYPE_CODE_COMPLEX:
      if (options->format)
	print_scalar_formatted (valaddr + embedded_offset,
				TYPE_TARGET_TYPE (type),
				options, 0, stream);
      else
	print_floating (valaddr + embedded_offset, TYPE_TARGET_TYPE (type),
			stream);
      fprintf_filtered (stream, " + ");
      if (options->format)
	print_scalar_formatted (valaddr + embedded_offset
				+ TYPE_LENGTH (TYPE_TARGET_TYPE (type)),
				TYPE_TARGET_TYPE (type),
				options, 0, stream);
      else
	print_floating (valaddr + embedded_offset
			+ TYPE_LENGTH (TYPE_TARGET_TYPE (type)),
			TYPE_TARGET_TYPE (type),
			stream);
      fprintf_filtered (stream, " * I");
      break;

    default:
      error (_("Invalid C/C++ type code %d in symbol table."), TYPE_CODE (type));
    }
  gdb_flush (stream);
  return (0);
}

int
c_value_print (struct value *val, struct ui_file *stream, 
	       const struct value_print_options *options)
{
  struct type *type, *real_type, *val_type;
  int full, top, using_enc;
  struct value_print_options opts = *options;

  opts.deref_ref = 1;

  /* If it is a pointer, indicate what it points to.

     Print type also if it is a reference.

     C++: if it is a member pointer, we will take care
     of that when we print it.  */

  /* Preserve the original type before stripping typedefs.  We prefer
     to pass down the original type when possible, but for local
     checks it is better to look past the typedefs.  */
  val_type = value_type (val);
  type = check_typedef (val_type);

  if (TYPE_CODE (type) == TYPE_CODE_PTR
      || TYPE_CODE (type) == TYPE_CODE_REF)
    {
      /* Hack:  remove (char *) for char strings.  Their
         type is indicated by the quoted string anyway.
         (Don't use c_textual_element_type here; quoted strings
         are always exactly (char *), (wchar_t *), or the like.  */
      if (TYPE_CODE (val_type) == TYPE_CODE_PTR
	  && TYPE_NAME (val_type) == NULL
	  && TYPE_NAME (TYPE_TARGET_TYPE (val_type)) != NULL
	  && (strcmp (TYPE_NAME (TYPE_TARGET_TYPE (val_type)), "char") == 0
	      || textual_name (TYPE_NAME (TYPE_TARGET_TYPE (val_type)))))
	{
	  /* Print nothing */
	}
      else if (options->objectprint
	       && (TYPE_CODE (TYPE_TARGET_TYPE (type)) == TYPE_CODE_CLASS))
	{

	  if (TYPE_CODE(type) == TYPE_CODE_REF)
	    {
	      /* Copy value, change to pointer, so we don't get an
	       * error about a non-pointer type in value_rtti_target_type
	       */
	      struct value *temparg;
	      temparg=value_copy(val);
	      deprecated_set_value_type (temparg, lookup_pointer_type (TYPE_TARGET_TYPE(type)));
	      val=temparg;
	    }
	  /* Pointer to class, check real type of object */
	  fprintf_filtered (stream, "(");
          real_type = value_rtti_target_type (val, &full, &top, &using_enc);
          if (real_type)
	    {
	      /* RTTI entry found */
              if (TYPE_CODE (type) == TYPE_CODE_PTR)
                {
                  /* create a pointer type pointing to the real type */
                  type = lookup_pointer_type (real_type);
                }
              else
                {
                  /* create a reference type referencing the real type */
                  type = lookup_reference_type (real_type);
                }
	      /* JYG: Need to adjust pointer value. */
	      /* NOTE: cagney/2005-01-02: THIS IS BOGUS.  */
              value_contents_writeable (val)[0] -= top;

              /* Note: When we look up RTTI entries, we don't get any 
                 information on const or volatile attributes */
            }
          type_print (type, "", stream, -1);
	  fprintf_filtered (stream, ") ");
	  val_type = type;
	}
      else
	{
	  /* normal case */
	  fprintf_filtered (stream, "(");
	  type_print (value_type (val), "", stream, -1);
	  fprintf_filtered (stream, ") ");
	}
    }

  /* APPLE LOCAL begin variable initialized status.  */
  if (value_var_status (val) == 0)
    fprintf_filtered (stream, " [uninitialized] ");
  /* APPLE LOCAL end variable initialized status.  */

  if (options->objectprint && (TYPE_CODE (type) == TYPE_CODE_CLASS))
    {
      /* Attempt to determine real type of object */
      real_type = value_rtti_type (val, &full, &top, &using_enc);
      if (real_type)
	{
	  /* We have RTTI information, so use it */
	  val = value_full_object (val, real_type, full, top, using_enc);
	  fprintf_filtered (stream, "(%s%s) ",
			    TYPE_NAME (real_type),
			    full ? "" : _(" [incomplete object]"));
	  /* Print out object: enclosing type is same as real_type if full */
	  return val_print (value_enclosing_type (val),
			    value_contents_all (val), 0,
			    VALUE_ADDRESS (val), stream, 0,
			    &opts, current_language);
          /* Note: When we look up RTTI entries, we don't get any information on
             const or volatile attributes */
	}
      else if (type != check_typedef (value_enclosing_type (val)))
	{
	  /* No RTTI information, so let's do our best */
	  fprintf_filtered (stream, "(%s ?) ",
			    TYPE_NAME (value_enclosing_type (val)));
	  return val_print (value_enclosing_type (val),
			    value_contents_all (val), 0,
			    VALUE_ADDRESS (val), stream, 0,
			    &opts, current_language);
	}
      /* Otherwise, we end up at the return outside this "if" */
    }

  real_type = get_closure_dynamic_type (val);
  if (real_type)
    type = real_type;

  return val_print (val_type, value_contents_all (val),
		    value_embedded_offset (val),
		    VALUE_ADDRESS (val) + value_offset (val),
		    stream, 0, &opts, current_language);
}
