/* Evaluate expressions for GDB.

   Copyright 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994,
   1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2005 Free
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

#include "defs.h"
#include "gdb_string.h"
#include "symtab.h"
#include "gdbtypes.h"
#include "value.h"
#include "expression.h"
#include "target.h"
#include "frame.h"
#include "language.h"		/* For CAST_IS_CONVERSION */
#include "f-lang.h"		/* for array bound stuff */
#include "cp-abi.h"
#include "infcall.h"
#include "objc-lang.h"
#include "block.h"
#include "parser-defs.h"
#include "cp-support.h"
#include "valprint.h"
#include "gdb_assert.h"

#include "gdb_assert.h"

/* This is defined in valops.c */
extern int overload_resolution;

/* Prototypes for local functions. */

static struct value *evaluate_subexp_for_sizeof (struct expression *, int *);

static struct value *evaluate_subexp_for_address (struct expression *,
						  int *, enum noside);

static struct value *evaluate_subexp (struct type *, struct expression *,
				      int *, enum noside);

static char *get_label (struct expression *, int *);

static struct value *evaluate_struct_tuple (struct value *,
					    struct expression *, int *,
					    enum noside, int);

static LONGEST init_array_element (struct value *, struct value *,
				   struct expression *, int *, enum noside,
				   LONGEST, LONGEST);

/* APPLE LOCAL: Closures.  */
int print_closure = 1;

static void
do_restore_print_closure (void *in_oldval)
{
  print_closure = (int) in_oldval;
}

struct cleanup *
make_cleanup_set_restore_print_closure (int newval)
{
  int oldval = print_closure;
  print_closure = newval;
  return make_cleanup (do_restore_print_closure, (void *) oldval);
}

static struct value *
evaluate_subexp (struct type *expect_type, struct expression *exp,
		 int *pos, enum noside noside)
{
  return (*exp->language_defn->la_exp_desc->evaluate_exp) 
    (expect_type, exp, pos, noside);
}

/* Parse the string EXP as a C expression, evaluate it,
   and return the result as a number.  */

CORE_ADDR
parse_and_eval_address (char *exp)
{
  /* APPLE LOCAL begin initialize innermost_block  */
  struct expression *expr;
  CORE_ADDR addr;
  struct cleanup *old_chain;

  innermost_block = NULL;
  expr = parse_expression (exp);
  old_chain = make_cleanup (free_current_contents, &expr);
  /* APPLE LOCAL end initialize innermost_block  */
  addr = value_as_address (evaluate_expression (expr));
  do_cleanups (old_chain);
  return addr;
}

/* Like parse_and_eval_address but takes a pointer to a char * variable
   and advanced that variable across the characters parsed.  */

CORE_ADDR
parse_and_eval_address_1 (char **expptr)
{
  /* APPLE LOCAL begin initialize innermost_block  */
  struct expression *expr;
  CORE_ADDR addr;
  struct cleanup *old_chain;

  innermost_block = NULL;
  expr = parse_exp_1 (expptr, (struct block *) 0, 0);
  old_chain = make_cleanup (free_current_contents, &expr);
  /* APPLE LOCAL end initialize innermost_block  */
  addr = value_as_address (evaluate_expression (expr));
  do_cleanups (old_chain);
  return addr;
}

/* Like parse_and_eval_address, but treats the value of the expression
   as an integer, not an address, returns a LONGEST, not a CORE_ADDR */
LONGEST
parse_and_eval_long (char *exp)
{
  /* APPLE LOCAL begin initialize innermost_block  */
  struct expression *expr;
  LONGEST retval;
  struct cleanup *old_chain;

  innermost_block = NULL;
  expr = parse_expression (exp);
  old_chain = make_cleanup (free_current_contents, &expr);
  /* APPLE LOCAL end initialize innermost_block  */
  retval = value_as_long (evaluate_expression (expr));
  do_cleanups (old_chain);
  return (retval);
}

struct value *
parse_and_eval (char *exp)
{
  /* APPLE LOCAL begin initialize innermost_block  */
  struct expression *expr;
  struct value *val;
  struct cleanup *old_chain;

  innermost_block = NULL;
  expr = parse_expression (exp);
  old_chain = make_cleanup (free_current_contents, &expr);
  /* APPLE LOCAL end initialize innermost_block  */
  val = evaluate_expression (expr);
  do_cleanups (old_chain);
  return val;
}

/* Parse up to a comma (or to a closeparen)
   in the string EXPP as an expression, evaluate it, and return the value.
   EXPP is advanced to point to the comma.  */

struct value *
parse_to_comma_and_eval (char **expp)
{
  /* APPLE LOCAL begin initialize innermost_block  */
  struct expression *expr;
  struct value *val;
  struct cleanup *old_chain;

  innermost_block = NULL;
  expr = parse_exp_1 (expp, (struct block *) 0, 1);
  old_chain = make_cleanup (free_current_contents, &expr);
  /* APPLE LOCAL end initialize innermost_block  */
  val = evaluate_expression (expr);
  do_cleanups (old_chain);
  return val;
}

/* Evaluate an expression in internal prefix form
   such as is constructed by parse.y.

   See expression.h for info on the format of an expression.  */

struct value *
evaluate_expression (struct expression *exp)
{
  int pc = 0;
  return evaluate_subexp (NULL_TYPE, exp, &pc, EVAL_NORMAL);
}

/* Evaluate an expression, avoiding all memory references
   and getting a value whose type alone is correct.  */

struct value *
evaluate_type (struct expression *exp)
{
  int pc = 0;
  return evaluate_subexp (NULL_TYPE, exp, &pc, EVAL_AVOID_SIDE_EFFECTS);
}

/* Evaluate a subexpression, avoiding all memory references and
   getting a value whose type alone is correct.  */

struct value *
evaluate_subexpression_type (struct expression *exp, int subexp)
{
  return evaluate_subexp (NULL_TYPE, exp, &subexp, EVAL_AVOID_SIDE_EFFECTS);
}

/* Extract a field operation from an expression.  If the subexpression
   of EXP starting at *SUBEXP is not a structure dereference
   operation, return NULL.  Otherwise, return the name of the
   dereferenced field, and advance *SUBEXP to point to the
   subexpression of the left-hand-side of the dereference.  This is
   used when completing field names.  */

char *
extract_field_op (struct expression *exp, int *subexp)
{
  int tem;
  char *result;
  if (exp->elts[*subexp].opcode != STRUCTOP_STRUCT
      && exp->elts[*subexp].opcode != STRUCTOP_PTR)
    return NULL;
  tem = longest_to_int (exp->elts[*subexp + 1].longconst);
  result = &exp->elts[*subexp + 2].string;
  (*subexp) += 1 + 3 + BYTES_TO_EXP_ELEM (tem + 1);
  return result;
}

/* If the next expression is an OP_LABELED, skips past it,
   returning the label.  Otherwise, does nothing and returns NULL. */

static char *
get_label (struct expression *exp, int *pos)
{
  if (exp->elts[*pos].opcode == OP_LABELED)
    {
      int pc = (*pos)++;
      char *name = &exp->elts[pc + 2].string;
      int tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 3 + BYTES_TO_EXP_ELEM (tem + 1);
      return name;
    }
  else
    return NULL;
}

/* This function evaluates tuples (in (the deleted) Chill) or
   brace-initializers (in C/C++) for structure types.  */

static struct value *
evaluate_struct_tuple (struct value *struct_val,
		       struct expression *exp,
		       int *pos, enum noside noside, int nargs)
{
  struct type *struct_type = check_typedef (value_type (struct_val));
  struct type *substruct_type = struct_type;
  struct type *field_type;
  int fieldno = -1;
  int variantno = -1;
  int subfieldno = -1;
  while (--nargs >= 0)
    {
      int pc = *pos;
      struct value *val = NULL;
      int nlabels = 0;
      int bitpos, bitsize;
      bfd_byte *addr;

      /* Skip past the labels, and count them. */
      while (get_label (exp, pos) != NULL)
	nlabels++;

      do
	{
	  char *label = get_label (exp, &pc);
	  if (label)
	    {
	      for (fieldno = 0; fieldno < TYPE_NFIELDS (struct_type);
		   fieldno++)
		{
		  char *field_name = TYPE_FIELD_NAME (struct_type, fieldno);
		  if (field_name != NULL && strcmp (field_name, label) == 0)
		    {
		      variantno = -1;
		      subfieldno = fieldno;
		      substruct_type = struct_type;
		      goto found;
		    }
		}
	      for (fieldno = 0; fieldno < TYPE_NFIELDS (struct_type);
		   fieldno++)
		{
		  char *field_name = TYPE_FIELD_NAME (struct_type, fieldno);
		  field_type = TYPE_FIELD_TYPE (struct_type, fieldno);
		  if ((field_name == 0 || *field_name == '\0')
		      && TYPE_CODE (field_type) == TYPE_CODE_UNION)
		    {
		      variantno = 0;
		      for (; variantno < TYPE_NFIELDS (field_type);
			   variantno++)
			{
			  substruct_type
			    = TYPE_FIELD_TYPE (field_type, variantno);
			  if (TYPE_CODE (substruct_type) == TYPE_CODE_STRUCT)
			    {
			      for (subfieldno = 0;
				 subfieldno < TYPE_NFIELDS (substruct_type);
				   subfieldno++)
				{
				  if (strcmp(TYPE_FIELD_NAME (substruct_type,
							      subfieldno),
					     label) == 0)
				    {
				      goto found;
				    }
				}
			    }
			}
		    }
		}
	      error (_("there is no field named %s"), label);
	    found:
	      ;
	    }
	  else
	    {
	      /* Unlabelled tuple element - go to next field. */
	      if (variantno >= 0)
		{
		  subfieldno++;
		  if (subfieldno >= TYPE_NFIELDS (substruct_type))
		    {
		      variantno = -1;
		      substruct_type = struct_type;
		    }
		}
	      if (variantno < 0)
		{
		  fieldno++;
		  subfieldno = fieldno;
		  if (fieldno >= TYPE_NFIELDS (struct_type))
		    error (_("too many initializers"));
		  field_type = TYPE_FIELD_TYPE (struct_type, fieldno);
		  if (TYPE_CODE (field_type) == TYPE_CODE_UNION
		      && TYPE_FIELD_NAME (struct_type, fieldno)[0] == '0')
		    error (_("don't know which variant you want to set"));
		}
	    }

	  /* Here, struct_type is the type of the inner struct,
	     while substruct_type is the type of the inner struct.
	     These are the same for normal structures, but a variant struct
	     contains anonymous union fields that contain substruct fields.
	     The value fieldno is the index of the top-level (normal or
	     anonymous union) field in struct_field, while the value
	     subfieldno is the index of the actual real (named inner) field
	     in substruct_type. */

	  field_type = TYPE_FIELD_TYPE (substruct_type, subfieldno);
	  if (val == 0)
	    val = evaluate_subexp (field_type, exp, pos, noside);

	  /* Now actually set the field in struct_val. */

	  /* Assign val to field fieldno. */
	  if (value_type (val) != field_type)
	    val = value_cast (field_type, val);

	  bitsize = TYPE_FIELD_BITSIZE (substruct_type, subfieldno);
	  bitpos = TYPE_FIELD_BITPOS (struct_type, fieldno);
	  if (variantno >= 0)
	    bitpos += TYPE_FIELD_BITPOS (substruct_type, subfieldno);
	  addr = value_contents_writeable (struct_val) + bitpos / 8;
	  if (bitsize)
	    modify_field (addr, value_as_long (val),
			  bitpos % 8, bitsize);
	  else
	    memcpy (addr, value_contents (val),
		    TYPE_LENGTH (value_type (val)));
	}
      while (--nlabels > 0);
    }
  return struct_val;
}

/* Recursive helper function for setting elements of array tuples for
   (the deleted) Chill.  The target is ARRAY (which has bounds
   LOW_BOUND to HIGH_BOUND); the element value is ELEMENT; EXP, POS
   and NOSIDE are as usual.  Evaluates index expresions and sets the
   specified element(s) of ARRAY to ELEMENT.  Returns last index
   value.  */

static LONGEST
init_array_element (struct value *array, struct value *element,
		    struct expression *exp, int *pos,
		    enum noside noside, LONGEST low_bound, LONGEST high_bound)
{
  LONGEST index;
  int element_size = TYPE_LENGTH (value_type (element));
  if (exp->elts[*pos].opcode == BINOP_COMMA)
    {
      (*pos)++;
      init_array_element (array, element, exp, pos, noside,
			  low_bound, high_bound);
      return init_array_element (array, element,
				 exp, pos, noside, low_bound, high_bound);
    }
  else if (exp->elts[*pos].opcode == BINOP_RANGE)
    {
      LONGEST low, high;
      (*pos)++;
      low = value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
      high = value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
      if (low < low_bound || high > high_bound)
	error (_("tuple range index out of range"));
      for (index = low; index <= high; index++)
	{
	  memcpy (value_contents_raw (array)
		  + (index - low_bound) * element_size,
		  value_contents (element), element_size);
	}
    }
  else
    {
      index = value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
      if (index < low_bound || index > high_bound)
	error (_("tuple index out of range"));
      memcpy (value_contents_raw (array) + (index - low_bound) * element_size,
	      value_contents (element), element_size);
    }
  return index;
}

struct value *
evaluate_subexp_standard (struct type *expect_type,
			  struct expression *exp, int *pos,
			  enum noside noside)
{
  enum exp_opcode op;
  int tem, tem2, tem3;
  int pc, pc2 = 0, oldpos;
  struct value *arg1 = NULL;
  struct value *arg2 = NULL;
  struct value *arg3;
  struct type *type;
  int nargs;
  struct value **argvec;
  int upper, lower, retcode;
  int code;
  int ix;
  long mem_offset;
  struct type **arg_types;
  int save_pos1;
  struct symbol *function = NULL;
  char *function_name = NULL;

  pc = (*pos)++;
  op = exp->elts[pc].opcode;

  switch (op)
    {
    case OP_SCOPE:
      tem = longest_to_int (exp->elts[pc + 2].longconst);
      (*pos) += 4 + BYTES_TO_EXP_ELEM (tem + 1);
      if (noside == EVAL_SKIP)
	goto nosideret;
      arg1 = value_aggregate_elt (exp->elts[pc + 1].type,
				  &exp->elts[pc + 3].string,
				  0, noside);
      if (arg1 == NULL)
	error (_("There is no field named %s"), &exp->elts[pc + 3].string);
      return arg1;

    case OP_LONG:
      (*pos) += 3;
      return value_from_longest (exp->elts[pc + 1].type,
				 exp->elts[pc + 2].longconst);

    case OP_DOUBLE:
      (*pos) += 3;
      return value_from_double (exp->elts[pc + 1].type,
				exp->elts[pc + 2].doubleconst);

    case OP_VAR_VALUE:
      (*pos) += 3;
      if (noside == EVAL_SKIP)
	goto nosideret;

      /* JYG: We used to just return value_zero of the symbol type
        if we're asked to avoid side effects.  Otherwise we return
        value_of_variable (...).  However I'm not sure if
        value_of_variable () has any side effect.
        We need a full value object returned here for whatis_exp ()
        to call evaluate_type () and then pass the full value to
        value_rtti_target_type () if we are dealing with a pointer
        or reference to a base class and print object is on. */
      {
	struct value *retval;
	struct type *dynamic_type;

        retval = value_of_variable (exp->elts[pc + 2].symbol,
                                  exp->elts[pc + 1].block);
	/* APPLE LOCAL - We don't want to print the closure type always.
	   This made things look better in command-line gdb but it
	   obscures the distinction between dynamic & static type
	   changes.  So we add this variable and toggle it off in 
	   the varobj code where this is important.  */
	if (print_closure)
	  {
	    dynamic_type = get_closure_dynamic_type (retval);
	    if (dynamic_type)
	      retval = value_cast (dynamic_type, retval);
	  }
	/* END APPLE LOCAL */
	return retval;
      }

    case OP_LAST:
      (*pos) += 2;
      return
	access_value_history (longest_to_int (exp->elts[pc + 1].longconst));

    case OP_REGISTER:
      {
	int regno = longest_to_int (exp->elts[pc + 1].longconst);
	struct value *val = value_of_register (regno, get_selected_frame (NULL));
	/* APPLE LOCAL begin literal register setting */
	/* Remember that this is a register being set directly by
	   name; for the benefit of G5s we will want to treat it as a
	   single 64-bit entity (even with 32-bit programs), rather
	   than following the ABI as we would do for a regular
	   variable stored in the register.  */
	VALUE_LVAL (val) = lval_register_literal;
	/* APPLE LOCAL end literal register setting */
	(*pos) += 2;
	if (val == NULL)
	  error (_("Value of register %s not available."),
		 frame_map_regnum_to_name (get_selected_frame (NULL), regno));
	else
	  return val;
      }
    case OP_BOOL:
      (*pos) += 2;
      return value_from_longest (LA_BOOL_TYPE,
				 exp->elts[pc + 1].longconst);

    case OP_INTERNALVAR:
      (*pos) += 2;
      return value_of_internalvar (exp->elts[pc + 1].internalvar);

    case OP_STRING:
      tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 3 + BYTES_TO_EXP_ELEM (tem + 1);
      if (noside == EVAL_SKIP)
	goto nosideret;
      return value_string (&exp->elts[pc + 2].string, tem);

      /* FIXME: I think above call is likely wrong, and should be 
         value_string (..., tem + 1);  I can't easily test it, since 
         while Fortran and Chill still use OP_STRING, C and C++ do not. */

    case OP_OBJC_NSSTRING:		/* Objective C Foundation Class NSString constant.  */
      tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 3 + BYTES_TO_EXP_ELEM (tem + 1);
      if (noside == EVAL_SKIP)
	{
	  goto nosideret;
	}
      return (struct value *) value_nsstring (&exp->elts[pc + 2].string, tem + 1);

    case OP_BITSTRING:
      tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos)
	+= 3 + BYTES_TO_EXP_ELEM ((tem + HOST_CHAR_BIT - 1) / HOST_CHAR_BIT);
      if (noside == EVAL_SKIP)
	goto nosideret;
      return value_bitstring (&exp->elts[pc + 2].string, tem);
      break;

    case OP_ARRAY:
      (*pos) += 3;
      tem2 = longest_to_int (exp->elts[pc + 1].longconst);
      tem3 = longest_to_int (exp->elts[pc + 2].longconst);
      nargs = tem3 - tem2 + 1;
      type = expect_type ? check_typedef (expect_type) : NULL_TYPE;

      if (expect_type != NULL_TYPE && noside != EVAL_SKIP
	  && TYPE_CODE (type) == TYPE_CODE_STRUCT)
	{
	  struct value *rec = allocate_value (expect_type);
	  memset (value_contents_raw (rec), '\0', TYPE_LENGTH (type));
	  return evaluate_struct_tuple (rec, exp, pos, noside, nargs);
	}

      if (expect_type != NULL_TYPE && noside != EVAL_SKIP
	  && TYPE_CODE (type) == TYPE_CODE_ARRAY)
	{
	  struct type *range_type = TYPE_FIELD_TYPE (type, 0);
	  struct type *element_type = TYPE_TARGET_TYPE (type);
	  struct value *array = allocate_value (expect_type);
	  int element_size = TYPE_LENGTH (check_typedef (element_type));
	  LONGEST low_bound, high_bound, index;
	  if (get_discrete_bounds (range_type, &low_bound, &high_bound) < 0)
	    {
	      low_bound = 0;
	      high_bound = (TYPE_LENGTH (type) / element_size) - 1;
	    }
	  index = low_bound;
	  memset (value_contents_raw (array), 0, TYPE_LENGTH (expect_type));
	  for (tem = nargs; --nargs >= 0;)
	    {
	      struct value *element;
	      int index_pc = 0;
	      if (exp->elts[*pos].opcode == BINOP_RANGE)
		{
		  index_pc = ++(*pos);
		  evaluate_subexp (NULL_TYPE, exp, pos, EVAL_SKIP);
		}
	      element = evaluate_subexp (element_type, exp, pos, noside);
	      if (value_type (element) != element_type)
		element = value_cast (element_type, element);
	      if (index_pc)
		{
		  int continue_pc = *pos;
		  *pos = index_pc;
		  index = init_array_element (array, element, exp, pos, noside,
					      low_bound, high_bound);
		  *pos = continue_pc;
		}
	      else
		{
		  if (index > high_bound)
		    /* to avoid memory corruption */
		    error (_("Too many array elements"));
		  memcpy (value_contents_raw (array)
			  + (index - low_bound) * element_size,
			  value_contents (element),
			  element_size);
		}
	      index++;
	    }
	  return array;
	}

      if (expect_type != NULL_TYPE && noside != EVAL_SKIP
	  && TYPE_CODE (type) == TYPE_CODE_SET)
	{
	  struct value *set = allocate_value (expect_type);
	  gdb_byte *valaddr = value_contents_raw (set);
	  struct type *element_type = TYPE_INDEX_TYPE (type);
	  struct type *check_type = element_type;
	  LONGEST low_bound, high_bound;

	  /* get targettype of elementtype */
	  while (TYPE_CODE (check_type) == TYPE_CODE_RANGE ||
		 TYPE_CODE (check_type) == TYPE_CODE_TYPEDEF)
	    check_type = TYPE_TARGET_TYPE (check_type);

	  if (get_discrete_bounds (element_type, &low_bound, &high_bound) < 0)
	    error (_("(power)set type with unknown size"));
	  memset (valaddr, '\0', TYPE_LENGTH (type));
	  for (tem = 0; tem < nargs; tem++)
	    {
	      LONGEST range_low, range_high;
	      struct type *range_low_type, *range_high_type;
	      struct value *elem_val;
	      if (exp->elts[*pos].opcode == BINOP_RANGE)
		{
		  (*pos)++;
		  elem_val = evaluate_subexp (element_type, exp, pos, noside);
		  range_low_type = value_type (elem_val);
		  range_low = value_as_long (elem_val);
		  elem_val = evaluate_subexp (element_type, exp, pos, noside);
		  range_high_type = value_type (elem_val);
		  range_high = value_as_long (elem_val);
		}
	      else
		{
		  elem_val = evaluate_subexp (element_type, exp, pos, noside);
		  range_low_type = range_high_type = value_type (elem_val);
		  range_low = range_high = value_as_long (elem_val);
		}
	      /* check types of elements to avoid mixture of elements from
	         different types. Also check if type of element is "compatible"
	         with element type of powerset */
	      if (TYPE_CODE (range_low_type) == TYPE_CODE_RANGE)
		range_low_type = TYPE_TARGET_TYPE (range_low_type);
	      if (TYPE_CODE (range_high_type) == TYPE_CODE_RANGE)
		range_high_type = TYPE_TARGET_TYPE (range_high_type);
	      if ((TYPE_CODE (range_low_type) != TYPE_CODE (range_high_type)) ||
		  (TYPE_CODE (range_low_type) == TYPE_CODE_ENUM &&
		   (range_low_type != range_high_type)))
		/* different element modes */
		error (_("POWERSET tuple elements of different mode"));
	      if ((TYPE_CODE (check_type) != TYPE_CODE (range_low_type)) ||
		  (TYPE_CODE (check_type) == TYPE_CODE_ENUM &&
		   range_low_type != check_type))
		error (_("incompatible POWERSET tuple elements"));
	      if (range_low > range_high)
		{
		  warning (_("empty POWERSET tuple range"));
		  continue;
		}
	      if (range_low < low_bound || range_high > high_bound)
		error (_("POWERSET tuple element out of range"));
	      range_low -= low_bound;
	      range_high -= low_bound;
	      for (; range_low <= range_high; range_low++)
		{
		  int bit_index = (unsigned) range_low % TARGET_CHAR_BIT;
		  if (BITS_BIG_ENDIAN)
		    bit_index = TARGET_CHAR_BIT - 1 - bit_index;
		  valaddr[(unsigned) range_low / TARGET_CHAR_BIT]
		    |= 1 << bit_index;
		}
	    }
	  return set;
	}

      argvec = (struct value **) alloca (sizeof (struct value *) * nargs);
      for (tem = 0; tem < nargs; tem++)
	{
	  /* Ensure that array expressions are coerced into pointer objects. */
	  argvec[tem] = evaluate_subexp_with_coercion (exp, pos, noside);
	}
      if (noside == EVAL_SKIP)
	goto nosideret;
      return value_array (tem2, tem3, argvec);

    case TERNOP_SLICE:
      {
	struct value *array = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	int lowbound
	= value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
	int upper
	= value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
	if (noside == EVAL_SKIP)
	  goto nosideret;
	return value_slice (array, lowbound, upper - lowbound + 1);
      }

    case TERNOP_SLICE_COUNT:
      {
	struct value *array = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	int lowbound
	= value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
	int length
	= value_as_long (evaluate_subexp (NULL_TYPE, exp, pos, noside));
	return value_slice (array, lowbound, length);
      }

    case TERNOP_COND:
      /* Skip third and second args to evaluate the first one.  */
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (value_logical_not (arg1))
	{
	  evaluate_subexp (NULL_TYPE, exp, pos, EVAL_SKIP);
	  return evaluate_subexp (NULL_TYPE, exp, pos, noside);
	}
      else
	{
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	  evaluate_subexp (NULL_TYPE, exp, pos, EVAL_SKIP);
	  return arg2;
	}

    case OP_OBJC_SELECTOR:
      {				/* Objective C @selector operator.  */
	char *sel = &exp->elts[pc + 2].string;
	int len = longest_to_int (exp->elts[pc + 1].longconst);

	(*pos) += 3 + BYTES_TO_EXP_ELEM (len + 1);
	if (noside == EVAL_SKIP)
	  goto nosideret;

	if (sel[len] != 0)
	  sel[len] = 0;		/* Make sure it's terminated.  */
	return value_from_longest (lookup_pointer_type (builtin_type_void),
				   lookup_child_selector (sel));
      }

    case OP_OBJC_MSGCALL:
      {				/* Objective C message (method) call.  */
	CORE_ADDR selector = 0;

	int struct_return = 0;
	int sub_no_side = 0;

	static int cached_values = 0;
	static struct cached_value *msg_send = NULL;
	static struct cached_value *msg_send_stret = NULL;
	static int gnu_runtime = 0;

	struct value *target = NULL;
	struct value *method = NULL;
	struct value *called_method = NULL; 

	struct type *selector_type = NULL;

	struct value *ret = NULL;
	CORE_ADDR addr = 0;

        /* APPLE LOCAL: SELECTOR can be sign-extended because .longconst
           is signed; mask off the upper 32 bits if we're not a 64 bit 
           program.  */
        if (TARGET_PTR_BIT == 64)
	  selector = exp->elts[pc + 1].longconst;
        else
	  selector = exp->elts[pc + 1].longconst & 0xffffffff;
	nargs = exp->elts[pc + 2].longconst;
	argvec = (struct value **) alloca (sizeof (struct value *) 
					   * (nargs + 5));

	(*pos) += 3;

	selector_type = lookup_pointer_type (builtin_type_void_data_ptr);
	if (noside == EVAL_AVOID_SIDE_EFFECTS)
	  sub_no_side = EVAL_NORMAL;
	else
	  sub_no_side = noside;

	target = evaluate_subexp (selector_type, exp, pos, sub_no_side);

	/* APPLE LOCAL: If we go on from here we are going to try to look
	   up TARGET as an objc class.  But getting the target (OP_VAR_VALUE)
	   when NOSIDE is EVAL_SKIP just returns "1", which is not going to 
	   work when we start grubbing around in memory there.  */
	if (noside == EVAL_SKIP)
	  goto nosideret;

	if (value_as_long (target) == 0)
 	  return value_from_longest (builtin_type_long, 0);

	if (! cached_values)
	  {

	    if (lookup_minimal_symbol ("objc_msg_lookup", 0, 0))
	      gnu_runtime = 1;

	    /* Find the method dispatch (Apple runtime) or method lookup
	       (GNU runtime) function for Objective-C.  These will be used
	       to lookup the symbol information for the method.  If we
	       can't find any symbol information, then we'll use these to
	       call the method, otherwise we can call the method
	       directly. The msg_send_stret function is used in the special
	       case of a method that returns a structure (Apple runtime 
	       only).  */
	    if (gnu_runtime)
	      {

		/* APPLE LOCAL: FIXME - it seems innocent enough to give
		   a type to the msg_send function here.  But the code 
		   below this will use the type of the cached function 
		   value as the type of the method call if debug symbols
		   for the call can't be found.  Look particularly where
		   we check for (!method) and then inherit called_method
		   from there.  I think THAT code is what is actually 
		   wrong, but it works correctly if you don't set the 
		   type here.  
		   So don't be tempted to move this bit of code out to the
		   Apple Runtime part of the code without fixing the
		   way called_method is used below.  */
	 
                struct type *type;
                type = lookup_pointer_type (builtin_type_void);
                type = lookup_function_type (type);
                type = lookup_pointer_type (type);
                type = lookup_function_type (type);
                type = lookup_pointer_type (type);
                msg_send = create_cached_function ("objc_msg_lookup", type);
                /* Special dispatcher for methods returning structs */
                msg_send_stret = create_cached_function ("objc_msg_lookup", type);
	      }
            else
              {
                msg_send = create_cached_function ("objc_msgSend", NULL);
                /* Special dispatcher for methods returning structs */
                msg_send_stret = create_cached_function ("objc_msgSend_stret", NULL);
              }

            cached_values = 1;
          }

        /* APPLE LOCAL: Instead of calling into the inferior two times
           before calling the method itself, let's just grope around in
           the ObjC runtime like we do elsewhere and speed everything up. */

        addr = find_implementation (value_as_address (target), selector, 0);
        if (addr == 0)
          error ("Target does not respond to this message selector.");

	if (addr)
	  {
	    struct symbol *sym = NULL;
	    /* is it a high_level symbol?  */

	    sym = find_pc_function (addr);
	    if (sym != NULL) 
	      method = value_of_variable (sym, 0);
	  }

	/* If we found a method with symbol information, check to see
           if it returns a struct.  Otherwise assume it doesn't.  */

	if (method)
	  {
	    struct block *b;
	    CORE_ADDR funaddr;
	    struct type *val_type;

	    funaddr = find_function_addr (method, &val_type);

	    b = block_for_pc (funaddr);

	    CHECK_TYPEDEF (val_type);
	  
	    if ((val_type == NULL) 
		|| (TYPE_CODE(val_type) == TYPE_CODE_ERROR))
	      {
		if (expect_type != NULL)
		  val_type = expect_type;
	      }

	    struct_return = using_struct_return (value_type (method), val_type);
	  }
	else if (expect_type != NULL)
	  {
	    struct_return = using_struct_return (NULL,
						 check_typedef (expect_type));
	  }
	
	/* Found a function symbol.  Now we will substitute its
	   value in place of the message dispatcher (obj_msgSend),
	   so that we call the method directly instead of thru
	   the dispatcher.  The main reason for doing this is that
	   we can now evaluate the return value and parameter values
	   according to their known data types, in case we need to
	   do things like promotion, dereferencing, special handling
	   of structs and doubles, etc.
	  
	   We want to use the type signature of 'method', but still
	   jump to objc_msgSend() or objc_msgSend_stret() to better
	   mimic the behavior of the runtime.  */
	
	if (method)
	  {
	    if (TYPE_CODE (value_type (method)) != TYPE_CODE_FUNC)
	      error (_("method address has symbol information with non-function type; skipping"));
	    if (struct_return)
	      VALUE_ADDRESS (method) = value_as_address (lookup_cached_function (msg_send_stret));
	    else
	      VALUE_ADDRESS (method) = value_as_address (lookup_cached_function (msg_send));
	    called_method = method;
	  }
	else
	  {
	    if (struct_return)
	      called_method = lookup_cached_function (msg_send_stret);
	    else
	      called_method = lookup_cached_function (msg_send);
	  }

	if (noside == EVAL_SKIP)
	  goto nosideret;

	if (noside == EVAL_AVOID_SIDE_EFFECTS)
	  {
	    /* If the return type doesn't look like a function type,
	       call an error.  This can happen if somebody tries to
	       turn a variable into a function call. This is here
	       because people often want to call, eg, strcmp, which
	       gdb doesn't know is a function.  If gdb isn't asked for
	       it's opinion (ie. through "whatis"), it won't offer
	       it. */

	    struct type *type = value_type (called_method);
	    if (type && TYPE_CODE (type) == TYPE_CODE_PTR)
	      type = TYPE_TARGET_TYPE (type);
	    type = TYPE_TARGET_TYPE (type);

	    if (type)
	    {
	      if ((TYPE_CODE (type) == TYPE_CODE_ERROR) && expect_type)
		return allocate_value (expect_type);
	      else
		return allocate_value (type);
	    }
	    else
	      error (_("Expression of type other than \"method returning ...\" used as a method"));
	  }

	/* Now depending on whether we found a symbol for the method,
	   we will either call the runtime dispatcher or the method
	   directly.  */

	argvec[0] = called_method;
	argvec[1] = target;
	argvec[2] = value_from_longest (builtin_type_long, selector);
	/* User-supplied arguments.  */
	for (tem = 0; tem < nargs; tem++)
	  argvec[tem + 3] = evaluate_subexp_with_coercion (exp, pos, noside);
	argvec[tem + 3] = 0;

	if (gnu_runtime && (method != NULL))
	  {
	    /* APPLE LOCAL begin */
	    ret = call_function_by_hand_expecting_type (argvec[0], builtin_type_void_func_ptr, nargs + 2, argvec + 1, 1);
	    argvec[0] = ret;
	  }
	ret = call_function_by_hand_expecting_type (argvec[0], expect_type, nargs + 2, argvec + 1, 1);
	/* APPLE LOCAL end */

	return ret;
      }
      break;

    case OP_FUNCALL:
      (*pos) += 2;
      op = exp->elts[*pos].opcode;
      nargs = longest_to_int (exp->elts[pc + 1].longconst);
      /* Allocate arg vector, including space for the function to be
         called in argvec[0] and a terminating NULL */
      argvec = (struct value **) alloca (sizeof (struct value *) * (nargs + 3));
      if (op == STRUCTOP_MEMBER || op == STRUCTOP_MPTR)
	{
	  /* 1997-08-01 Currently we do not support function invocation
	     via pointers-to-methods with HP aCC. Pointer does not point
	     to the function, but possibly to some thunk. */
	  if (deprecated_hp_som_som_object_present)
	    {
	      error (_("Not implemented: function invocation through pointer to method with HP aCC"));
	    }

	  nargs++;
	  /* First, evaluate the structure into arg2 */
	  pc2 = (*pos)++;

	  if (noside == EVAL_SKIP)
	    goto nosideret;

	  if (op == STRUCTOP_MEMBER)
	    {
	      arg2 = evaluate_subexp_for_address (exp, pos, noside);
	    }
	  else
	    {
	      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	    }

	  /* If the function is a virtual function, then the
	     aggregate value (providing the structure) plays
	     its part by providing the vtable.  Otherwise,
	     it is just along for the ride: call the function
	     directly.  */

	  arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);

#ifdef OLD_EMBARCADERO_CODE
	  fnptr = value_as_long (arg1);

	  if (METHOD_PTR_IS_VIRTUAL (fnptr))
	    {
	      int fnoffset = METHOD_PTR_TO_VOFFSET (fnptr);
	      struct type *basetype;
	      struct type *domain_type =
	      TYPE_DOMAIN_TYPE (TYPE_TARGET_TYPE (value_type (arg1)));
	      int i, j;
	      basetype = TYPE_TARGET_TYPE (value_type (arg2));
	      if (domain_type != basetype)
		arg2 = value_cast (lookup_pointer_type (domain_type), arg2);
	      basetype = TYPE_VPTR_BASETYPE (domain_type);
	      for (i = TYPE_NFN_FIELDS (basetype) - 1; i >= 0; i--)
		{
		  struct fn_field *f = TYPE_FN_FIELDLIST1 (basetype, i);
		  /* If one is virtual, then all are virtual.  */
		  if (TYPE_FN_FIELD_VIRTUAL_P (f, 0))
		    for (j = TYPE_FN_FIELDLIST_LENGTH (basetype, i) - 1; j >= 0; --j)
		      if ((int) TYPE_FN_FIELD_VOFFSET (f, j) == fnoffset)
			{
			  struct value *temp = value_ind (arg2);
			  arg1 = value_virtual_fn_field (&temp, f, j, domain_type, 0);
			  arg2 = value_addr (temp);
			  /* EMBARCADERO Local: begin Delphi class methods */
			  if (TYPE_FN_FIELD_METACLASS(f, j))
			    {
			      /* FIXME: need to evaluate
				 arg2 = evaluate( __classid(arg2) ); */
			      error (_("Not implemented: function invocation of virtual class methods"));
			    }
			  /* EMBARCADERO Local: end Delphi class methods */
			  goto got_it;
			}
		}
	      if (i < 0)
		error (_("virtual function at index %d not found"), fnoffset);
	    }
	got_it:
#else
	  if (TYPE_CODE (check_typedef (value_type (arg1)))
	      != TYPE_CODE_METHODPTR)
	    error (_("Non-pointer-to-member value used in pointer-to-member "
		     "construct"));
	  /* EMBARCADERO FIXME: need to test for Delphi class methods */
	  /* EMBARCADERO FIXME: need to test for Delphi nested functions */

	  if (noside == EVAL_AVOID_SIDE_EFFECTS)
	    {
	      struct type *method_type = check_typedef (value_type (arg1));
	      arg1 = value_zero (method_type, not_lval);
	    }
	  else
	    arg1 = cplus_method_ptr_to_value (&arg2, arg1);
#endif

	  /* Now, say which argument to start evaluating from */
	  tem = 2;
	}
      else if (op == STRUCTOP_STRUCT || op == STRUCTOP_PTR)
	{
	  /* Hair for method invocations */
	  int tem2;

	  nargs++;
	  /* First, evaluate the structure into arg2 */
	  pc2 = (*pos)++;
	  tem2 = longest_to_int (exp->elts[pc2 + 1].longconst);
	  *pos += 3 + BYTES_TO_EXP_ELEM (tem2 + 1);
	  if (noside == EVAL_SKIP)
	    goto nosideret;

	  if (op == STRUCTOP_STRUCT)
	    {
	      /* If v is a variable in a register, and the user types
	         v.method (), this will produce an error, because v has
	         no address.

	         A possible way around this would be to allocate a
	         copy of the variable on the stack, copy in the
	         contents, call the function, and copy out the
	         contents.  I.e. convert this from call by reference
	         to call by copy-return (or whatever it's called).
	         However, this does not work because it is not the
	         same: the method being called could stash a copy of
	         the address, and then future uses through that address
	         (after the method returns) would be expected to
	         use the variable itself, not some copy of it.  */
	      arg2 = evaluate_subexp_for_address (exp, pos, noside);
	    }
	  else
	    {
	      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	    }
	  /* Now, say which argument to start evaluating from */
	  tem = 2;
	}
      /* EMBARCADERO Local begin overload resolution in namespaces */
      else if (op == OP_SCOPE
	       && overload_resolution
	       && (exp->language_defn->la_language == language_cplus
		   /* APPLE LOCAL ObjC++ */
		   || exp->language_defn->la_language == language_objcplus
		   /* EMBARCADERO LOCAL Delphi units */
		   || exp->language_defn->la_language == language_pascal))
	{
	  /* Unpack it locally so we can properly handle overload
	     resolution.  */
	  char *name;
	  int local_tem;

	  pc2 = (*pos)++;
	  local_tem = longest_to_int (exp->elts[pc2 + 2].longconst);
	  (*pos) += 4 + BYTES_TO_EXP_ELEM (local_tem + 1);
	  type = exp->elts[pc2 + 1].type;
	  name = &exp->elts[pc2 + 3].string;

	  function = NULL;
	  function_name = NULL;
	  if (TYPE_CODE (type) == TYPE_CODE_NAMESPACE)
	    {
	      function = cp_lookup_symbol_namespace (TYPE_TAG_NAME (type),
						     name,
						     NULL,
						     get_selected_block (0),
						     VAR_DOMAIN,
						     1,
						     NULL);
	      if (function == NULL)
		error (_("No symbol \"%s\" in namespace \"%s\"."), 
		       name, TYPE_TAG_NAME (type));

	      tem = 1;
	    }
	  else
	    {
	      gdb_assert (TYPE_CODE (type) == TYPE_CODE_STRUCT
			  || TYPE_CODE (type) == TYPE_CODE_UNION);
	      function_name = name;

	      arg2 = value_zero (type, lval_memory);
	      ++nargs;
	      tem = 2;
	    }
	}
      /* EMBARCADERO Local end overload resolution in namespaces */
      else
	{
	  /* Non-method function call */
	  save_pos1 = *pos;
	  argvec[0] = evaluate_subexp_with_coercion (exp, pos, noside);
	  tem = 1;
	  type = value_type (argvec[0]);
	  if (type && TYPE_CODE (type) == TYPE_CODE_PTR)
	    type = TYPE_TARGET_TYPE (type);
	  if (type && TYPE_CODE (type) == TYPE_CODE_FUNC)
	    {
	      for (; tem <= nargs && tem <= TYPE_NFIELDS (type); tem++)
		{
		  /* pai: FIXME This seems to be coercing arguments before
		   * overload resolution has been done! */
		  argvec[tem] = evaluate_subexp (TYPE_FIELD_TYPE (type, tem - 1),
						 exp, pos, noside);
		}
	    }
	  /* EMBARCADERO LOCAL: begin non-function calls */
	  else
	    {
	      /* Don't allow function calls to * non-functions.  */
	      error (_("Invalid function call"));
	    }
	  /* EMBARCADERO LOCAL: end non-function calls */
	}

      /* Evaluate arguments */
      for (; tem <= nargs; tem++)
	{
	  /* Ensure that array expressions are coerced into pointer objects. */
	  argvec[tem] = evaluate_subexp_with_coercion (exp, pos, noside);
	}

      /* signal end of arglist */
      argvec[tem] = 0;

      if (op == STRUCTOP_STRUCT || op == STRUCTOP_PTR
	  /* EMBARCADERO Local overload resolution in namespaces */
	  || (op == OP_SCOPE && function_name != NULL))
	{
	  int memfuncflagsp;
	  char *tstr;

	  /* Method invocation : stuff "this" as first parameter.  */
	  argvec[1] = arg2;

	  if (op != OP_SCOPE)
	    {
	      /* Name of method from expression.  */
	      tstr = &exp->elts[pc2 + 2].string;
	    }
	  else
	    tstr = function_name;

	  if (overload_resolution && (exp->language_defn->la_language
				      == language_cplus
				      /* APPLE LOCAL ObjC++ */
				      || exp->language_defn->la_language
				      == language_objcplus
				      /* EMBARCADERO Local Delphi units */
				      || (exp->language_defn->la_language
				          == language_pascal
				          && op == OP_SCOPE)
				      ))
	    {
	      /* Language is C++, do some overload resolution before
		 evaluation.  */
	      struct value *valp = NULL;

	      /* Prepare list of argument types for overload resolution.  */
	      arg_types = (struct type **)
		alloca (nargs * (sizeof (struct type *)));
	      for (ix = 1; ix <= nargs; ix++)
		arg_types[ix - 1] = value_type (argvec[ix]);

	      (void) find_overload_match (arg_types, nargs, tstr,
	                                  1,	  /* method */
					  0,      /* strict match */
					  &arg2,  /* the object */
					  NULL, &valp, NULL,
					  &memfuncflagsp);

	      if (op == OP_SCOPE && !METHOD_IS_STATIC(memfuncflagsp))
		{
		  /* For the time being, we don't handle this.  */
		  error (_("Call to overloaded function %s requires "
			   "`this' pointer"),
			 function_name);
		}
	      /* EMBARCADERO Local: begin Delphi class methods */
	      else if (METHOD_IS_CLASSMETHOD(memfuncflagsp))
		{
		  /* FIXME: need to evaluate
		    argvec[1] = arg2 = evaluate( __classid(arg2) ); */
		  error (_("Not implemented: function invocation of class methods."));
		}
	      /* EMBARCADERO Local: end Delphi class methods */
	      argvec[1] = arg2;	/* the ``this'' pointer */
	      argvec[0] = valp;	/* Use the method found after overload
				   resolution.  */
	    }
	  else
	    /* Non-C++ case -- or no overload resolution.  */
	    {
	      struct value *temp = arg2;

	      argvec[0] = value_struct_elt (&temp, argvec + 1, tstr,
					    &memfuncflagsp,
					    op == STRUCTOP_STRUCT
				       ? "structure" : "structure pointer");
	      /* value_struct_elt updates temp with the correct value
	 	 of the ``this'' pointer if necessary, so modify argvec[1] to
		 reflect any ``this'' changes.  */
	      arg2
		= value_from_longest (lookup_pointer_type(value_type (temp)),
				      VALUE_ADDRESS (temp) + value_offset (temp)
				      + value_embedded_offset (temp));
	      argvec[1] = arg2;	/* the ``this'' pointer */
	    }

	  if (METHOD_IS_STATIC(memfuncflagsp))
	    {
	      argvec[1] = argvec[0];
	      nargs--;
	      argvec++;
	    }
	  /* EMBARCADERO Local: begin Delphi class methods */
	  else if (METHOD_IS_CLASSMETHOD(memfuncflagsp))
	    {
	      /* FIXME: need to evaluate
	         argvec[1] = arg2 = evaluate( __classid(arg2) ); */
	      error (_("Not implemented: function invocation of class methods."));
	    }
	  /* EMBARCADERO Local: end Delphi class methods */
	  /* EMBARCADERO Local begin don't call NULL this */
	  else
	    {
	      /* FIXME: also need to check for NULL this in case of virtual func.  */
	      if (value_as_address(argvec[1]) == 0)
		error (_("Can't call method with NULL this pointer."));
	    }
	  /* EMBARCADERO Local end don't call NULL this */
	}
      else if (op == STRUCTOP_MEMBER || op == STRUCTOP_MPTR)
	{
	  argvec[1] = arg2;
	  argvec[0] = arg1;
	}
      else if (op == OP_VAR_VALUE || (op == OP_SCOPE && function != NULL))
	{
	  /* Non-member function being called.  */
          /* fn: This can only be done for C++ functions.  A C-style function
             in a C++ program, for instance, does not have the fields that 
             are expected here.  */

	  if (overload_resolution && (exp->language_defn->la_language
				      == language_cplus
				      /* APPLE LOCAL ObjC++ */
				      || exp->language_defn->la_language
				      == language_objcplus
				      /* EMBARCADERO LOCAL Delphi units */
				      || exp->language_defn->la_language
				      == language_pascal))
	    {
	      /* Do some overload resolution before evaluation.  */
	      struct symbol *symp;

	      if (op == OP_VAR_VALUE)
		function = exp->elts[save_pos1+2].symbol;

	      /* Prepare list of argument types for overload resolution.  */
	      arg_types = (struct type **)
		alloca (nargs * (sizeof (struct type *)));
	      for (ix = 1; ix <= nargs; ix++)
		arg_types[ix - 1] = value_type (argvec[ix]);

	      (void) find_overload_match (arg_types, nargs,
					  NULL,        /* no need for name */
	                                  0,	       /* not method */
					  0,           /* strict match */
	                                  NULL, function, /* the function */
					  NULL, &symp, NULL);

	      if (op == OP_VAR_VALUE)
		{
		  /* Now fix the expression being evaluated.  */
		  exp->elts[save_pos1+2].symbol = symp;
		  argvec[0] = evaluate_subexp_with_coercion (exp, &save_pos1,
							     noside);
		}
	      else
		/* EMBARCADERO Local overload resolution in namespaces */
		argvec[0] = value_of_variable (symp, get_selected_block (0));
	    }
	  else
	    {
	      /* Not C++, or no overload resolution allowed.  */
	      /* Nothing to be done; argvec already correctly set up.  */
	    }
	}
      else
	{
	  /* It is probably a C-style function */
	  /* nothing to be done; argvec already correctly set up */
	}

    do_call_it:

      if (noside == EVAL_SKIP)
	goto nosideret;
      if (argvec[0] == NULL)
	error (_("Cannot evaluate function -- may be inlined"));
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	{
	  /* If the return type doesn't look like a function type, call an
	     error.  This can happen if somebody tries to turn a variable into
	     a function call. This is here because people often want to
	     call, eg, strcmp, which gdb doesn't know is a function.  If
	     gdb isn't asked for it's opinion (ie. through "whatis"),
	     it won't offer it. */

	  struct type *type = value_type (argvec[0]);
	  type = TYPE_TARGET_TYPE (type);

	  if (type)
	    {
	      if ((TYPE_CODE (type) == TYPE_CODE_ERROR) && expect_type)
		return allocate_value (expect_type);
	      else
		return allocate_value (type);
	    }
	  else
	    error (_("Expression of type other than \"Function returning ...\" used as function"));
	}
      if (argvec[0] == NULL)
	error ("Cannot evaluate function -- may be inlined");
      return call_function_by_hand_expecting_type (argvec[0], expect_type, nargs, argvec + 1, 1);
      /* pai: FIXME save value from call_function_by_hand, then adjust pc by adjust_fn_pc if +ve  */

    case OP_F77_UNDETERMINED_ARGLIST:

      /* Remember that in F77, functions, substring ops and 
         array subscript operations cannot be disambiguated 
         at parse time.  We have made all array subscript operations, 
         substring operations as well as function calls  come here 
         and we now have to discover what the heck this thing actually was.  
         If it is a function, we process just as if we got an OP_FUNCALL. */

      nargs = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 2;

      /* First determine the type code we are dealing with.  */
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      type = check_typedef (value_type (arg1));
      code = TYPE_CODE (type);

      if (code == TYPE_CODE_PTR)
	{
	  /* Fortran always passes variable to subroutines as pointer.
	     So we need to look into its target type to see if it is
	     array, string or function.  If it is, we need to switch
	     to the target value the original one points to.  */ 
	  struct type *target_type = check_typedef (TYPE_TARGET_TYPE (type));

	  if (TYPE_CODE (target_type) == TYPE_CODE_ARRAY
	      || TYPE_CODE (target_type) == TYPE_CODE_STRING
	      || TYPE_CODE (target_type) == TYPE_CODE_FUNC)
	    {
	      arg1 = value_ind (arg1);
	      type = check_typedef (value_type (arg1));
	      code = TYPE_CODE (type);
	    }
	} 

      switch (code)
	{
	case TYPE_CODE_ARRAY:
	  goto multi_f77_subscript;

	case TYPE_CODE_STRING:
	  goto op_f77_substr;

	case TYPE_CODE_PTR:
	case TYPE_CODE_FUNC:
	  /* It's a function call. */
	  /* Allocate arg vector, including space for the function to be
	     called in argvec[0] and a terminating NULL */
	  argvec = (struct value **) alloca (sizeof (struct value *) * (nargs + 2));
	  argvec[0] = arg1;
	  tem = 1;
	  for (; tem <= nargs; tem++)
	    argvec[tem] = evaluate_subexp_with_coercion (exp, pos, noside);
	  argvec[tem] = 0;	/* signal end of arglist */
	  goto do_call_it;

	default:
	  error (_("Cannot perform substring on this type"));
	}
    /* EMBARCADERO LOCAL: begin Multi-dimensional Pascal arrays */
    case OP_PASCAL_UNDETERMINED_ARGLIST:   
      {
	nargs = longest_to_int (exp->elts[pc + 1].longconst);
	(*pos) += 2;

	/* First determine the type code we are dealing with.  */
	arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	type = check_typedef (value_type (arg1));
	code = TYPE_CODE (type);

	int ndimensions = 1, i;
	struct value *array = arg1;

	/* Taken from Fortran code, which use similar approach working with 
	   multi dimenstional arrays */
	ndimensions = calc_f77_array_dims (type);

	if (nargs > ndimensions)
	  error (_("Wrong number of subscripts"));

	gdb_assert (nargs > 0);

	/* Now that we know we have a legal array subscript expression 
	   let us actually find out where this element exists in the array.  */

	LONGEST index = 0;
	/* Take array indices left to right.  */
	for (i = 0; i < nargs; i++)
	  {
	    struct type *array_type = check_typedef (value_type (array));
	    /* Evaluate each subscript; it must be a legal integer.  */
	    arg2 = evaluate_subexp_with_coercion (exp, pos, noside);

	    /* Fill in the subscript array.  */
	    index = value_as_long(arg2);

	    /* Taken from Fortran code, which use similar approach working with 
	       multi dimenstional arrays */
	    f77_get_dynamic_lowerbound (array_type, &lower);
	    f77_get_dynamic_upperbound (array_type, &upper);
	    if (lower > index || index > upper)
	      error (_("Violates subrange bounds"));
	    if ( i < nargs - 1)
	      array = value_subscripted_rvalue (array, arg2);
	  }
	return value_subscript(array, arg2);
    }
    /* EMBARCADERO LOCAL: end Multi-dimensional Pascal arrays */

    op_f77_substr:
      /* We have a substring operation on our hands here, 
         let us get the string we will be dealing with */

      /* Now evaluate the 'from' and 'to' */

      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);

      if (nargs < 2)
	return value_subscript (arg1, arg2);

      arg3 = evaluate_subexp_with_coercion (exp, pos, noside);

      if (noside == EVAL_SKIP)
	goto nosideret;

      tem2 = value_as_long (arg2);
      tem3 = value_as_long (arg3);

      return value_slice (arg1, tem2, tem3 - tem2 + 1);

    case OP_COMPLEX:
      /* We have a complex number, There should be 2 floating 
         point numbers that compose it */
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);

      return value_literal_complex (arg1, arg2, builtin_type_f_complex_s16);

    case STRUCTOP_STRUCT:
      tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 3 + BYTES_TO_EXP_ELEM (tem + 1);
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	return value_zero (lookup_struct_elt_type (value_type (arg1),
						   &exp->elts[pc + 2].string,
						   0),
			   lval_memory);
      else
	{
	  struct value *temp = arg1;
          /* EMBARCADERO LOCAL: support for properties. */
	  if (exp->lval_needed)
	    return value_struct_elt_as_lval (&temp, NULL, &exp->elts[pc + 2].string,
					     NULL, "structure");
	  else
	    return value_struct_elt (&temp, NULL, &exp->elts[pc + 2].string,
				     NULL, "structure");
	}

    case STRUCTOP_PTR:
      tem = longest_to_int (exp->elts[pc + 1].longconst);
      (*pos) += 3 + BYTES_TO_EXP_ELEM (tem + 1);
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;

      /* JYG: if print object is on we need to replace the base type
	 with rtti type in order to continue on with successful
	 lookup of member / method only available in the rtti type. */
      {
        struct type *type = value_type (arg1);
        struct type *real_type = NULL;
        int full, top, using_enc;
	struct value_print_options opts;

	get_user_print_options (&opts);
        if (opts.objectprint && TYPE_TARGET_TYPE(type) &&
            (TYPE_CODE (TYPE_TARGET_TYPE (type)) == TYPE_CODE_CLASS))
          {
            real_type = value_rtti_target_type (arg1, &full, &top, &using_enc);
            if (real_type)
              {
                if (TYPE_CODE (type) == TYPE_CODE_PTR)
                  real_type = lookup_pointer_type (real_type);
                else
                  real_type = lookup_reference_type (real_type);

                arg1 = value_cast (real_type, arg1);
              }
          }
	if (!real_type && print_closure)
	  {
	    real_type = get_closure_dynamic_type (arg1);
	    if (real_type)
	      arg1 = value_cast (real_type, arg1);
	  }
      }

      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	return value_zero (lookup_struct_elt_type (value_type (arg1),
						   &exp->elts[pc + 2].string,
						   0),
			   lval_memory);
      else
	{
	  struct value *temp = arg1;
          /* EMBARCADERO LOCAL: support for properties. */
	  if (exp->lval_needed)
	    return value_struct_elt_as_lval (&temp, NULL, &exp->elts[pc + 2].string,
				             NULL, "structure pointer");
	  else
	    return value_struct_elt (&temp, NULL, &exp->elts[pc + 2].string,
				     NULL, "structure pointer");
	}

    case STRUCTOP_MEMBER:
    case STRUCTOP_MPTR:
      if (op == STRUCTOP_MEMBER)
	arg1 = evaluate_subexp_for_address (exp, pos, noside);
      else
	arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);

      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);

      if (noside == EVAL_SKIP)
	goto nosideret;

      type = check_typedef (value_type (arg2));
      switch (TYPE_CODE (type))
	{
	case TYPE_CODE_METHODPTR:
	  if (deprecated_hp_som_som_object_present)
	    {
	      /* With HP aCC, pointers to methods do not point to the
		 function code.  */
	      /* 1997-08-19 */
	      error (_("Pointers to methods not supported with HP aCC"));
	    }

	  if (noside == EVAL_AVOID_SIDE_EFFECTS)
	    return value_zero (TYPE_TARGET_TYPE (type), not_lval);
	  else
	    {
	      arg2 = cplus_method_ptr_to_value (&arg1, arg2);
	      gdb_assert (TYPE_CODE (value_type (arg2)) == TYPE_CODE_PTR);
	      return value_ind (arg2);
	    }

	case TYPE_CODE_MEMBERPTR:
	  /* Now, convert these values to an address.  */
	  arg1 = value_cast (lookup_pointer_type (TYPE_DOMAIN_TYPE (type)),
			     arg1);

	  mem_offset = value_as_long (arg2);
	  if (deprecated_hp_som_som_object_present)
	    {
	      /* HP aCC generates offsets that have bit #29 set; turn it off to get
		 a real offset to the member. */
	      if (!mem_offset)	/* no bias -> really null */
		error (_("Attempted dereference of null pointer-to-member"));
	      mem_offset &= ~0x20000000;
	    }

	  arg3 = value_from_pointer (lookup_pointer_type (TYPE_TARGET_TYPE (type)),
				     value_as_long (arg1) + mem_offset);
	  return value_ind (arg3);

	default:
	  error (_("non-pointer-to-member value used in pointer-to-member construct"));
	}

    case BINOP_CONCAT:
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else
	return value_concat (arg1, arg2);

    case BINOP_ASSIGN:
      /* EMBARCADERO LOCAL: support for properties.
         If we're assigning to a property, setting lval_needed will 
         cause the setter to get called inside search_struct_property().
         For other assignments to properties, we just error out.  */
      exp->lval_needed = 1;	/* Need a value we can write to */
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);

      /* EMBARCADERO LOCAL: support for properties.  */
      /* FIXME: what will happen here after a setter is called?  */
      exp->lval_needed = 0;

      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);

      /* Do special stuff for HP aCC pointers to members */
      if (deprecated_hp_som_som_object_present)
	{
	  /* 1997-08-19 Can't assign HP aCC pointers to methods. No details of
	     the implementation yet; but the pointer appears to point to a code
	     sequence (thunk) in memory -- in any case it is *not* the address
	     of the function as it would be in a naive implementation. */
	  if (TYPE_CODE (value_type (arg1)) == TYPE_CODE_METHODPTR)
	    error (_("Assignment to pointers to methods not implemented with HP aCC"));

	  /* HP aCC pointers to data members require a constant bias.  */
	  if (TYPE_CODE (value_type (arg1)) == TYPE_CODE_MEMBERPTR)
	    {
	      unsigned int *ptr = (unsigned int *) value_contents (arg2);	/* forces evaluation */
	      *ptr |= 0x20000000;	/* set 29th bit */
	    }
	}

      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else
	return value_assign (arg1, arg2);

    case BINOP_ASSIGN_MODIFY:
      (*pos) += 2;
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      op = exp->elts[pc + 1].opcode;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, BINOP_ASSIGN_MODIFY, op, noside);
      else if (op == BINOP_ADD)
	arg2 = value_add (arg1, arg2);
      else if (op == BINOP_SUB)
	arg2 = value_sub (arg1, arg2);
      else
	arg2 = value_binop (arg1, arg2, op);
      return value_assign (arg1, arg2);

    case BINOP_ADD:
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else
	return value_add (arg1, arg2);

    case BINOP_SUB:
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else
	return value_sub (arg1, arg2);

    case BINOP_EXP:
    case BINOP_MUL:
    case BINOP_DIV:
    case BINOP_REM:
    case BINOP_MOD:
    case BINOP_LSH:
    case BINOP_RSH:
    case BINOP_BITWISE_AND:
    case BINOP_BITWISE_IOR:
    case BINOP_BITWISE_XOR:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else if (noside == EVAL_AVOID_SIDE_EFFECTS
	       && (op == BINOP_DIV || op == BINOP_REM || op == BINOP_MOD))
	return value_zero (value_type (arg1), not_lval);
      else
	return value_binop (arg1, arg2, op);

    case BINOP_RANGE:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      error (_("':' operator used in invalid context"));

    case BINOP_SUBSCRIPT:
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      type = check_typedef (value_type (arg1));
      if (binop_user_defined_p (op, arg1, arg2) && !c_delphi_string_type(type))
	return value_x_binop (arg1, arg2, op, OP_NULL, noside);
      else
	{
	  /* If the user attempts to subscript something that is not an
	     array or pointer type (like a plain int variable for example),
	     then report this as an error. */

	  arg1 = coerce_ref (arg1);
	  type = check_typedef (value_type (arg1));
	  if (TYPE_CODE (type) != TYPE_CODE_ARRAY
	      && TYPE_CODE (type) != TYPE_CODE_PTR
	      /* EMBARCASERO LOCAL Delphi strings */
	      && TYPE_CODE (type) != TYPE_CODE_STRING
	      /* EMBARCADERO LOCAL: Delphi Strings in C++ */                        
	      && !c_delphi_string_type(type))
	    {
	      if (TYPE_NAME (type))
		error (_("cannot subscript something of type `%s'"),
		       TYPE_NAME (type));
	      else
		error (_("cannot subscript requested type"));
	    }

	  if (noside == EVAL_AVOID_SIDE_EFFECTS)
	    return value_zero (TYPE_TARGET_TYPE (type), VALUE_LVAL (arg1));
	  else
	    return value_subscript (arg1, arg2);
	}

    case BINOP_IN:
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      return value_in (arg1, arg2);

    case MULTI_SUBSCRIPT:
      (*pos) += 2;
      nargs = longest_to_int (exp->elts[pc + 1].longconst);
      arg1 = evaluate_subexp_with_coercion (exp, pos, noside);
      while (nargs-- > 0)
	{
	  arg2 = evaluate_subexp_with_coercion (exp, pos, noside);
	  /* FIXME:  EVAL_SKIP handling may not be correct. */
	  if (noside == EVAL_SKIP)
	    {
	      if (nargs > 0)
		{
		  continue;
		}
	      else
		{
		  goto nosideret;
		}
	    }
	  /* FIXME:  EVAL_AVOID_SIDE_EFFECTS handling may not be correct. */
	  if (noside == EVAL_AVOID_SIDE_EFFECTS)
	    {
	      /* If the user attempts to subscript something that has no target
	         type (like a plain int variable for example), then report this
	         as an error. */

	      type = TYPE_TARGET_TYPE (check_typedef (value_type (arg1)));
	      if (type != NULL)
		{
		  arg1 = value_zero (type, VALUE_LVAL (arg1));
		  noside = EVAL_SKIP;
		  continue;
		}
	      else
		{
		  error (_("cannot subscript something of type `%s'"),
			 TYPE_NAME (value_type (arg1)));
		}
	    }

	  if (binop_user_defined_p (op, arg1, arg2))
	    {
	      arg1 = value_x_binop (arg1, arg2, op, OP_NULL, noside);
	    }
	  else
	    {
	      arg1 = value_subscript (arg1, arg2);
	    }
	}
      return (arg1);

    multi_f77_subscript:
      {
	int subscript_array[MAX_FORTRAN_DIMS];
	int array_size_array[MAX_FORTRAN_DIMS];
	int ndimensions = 1, i;
	struct type *tmp_type;
	int offset_item;	/* The array offset where the item lives */

	if (nargs > MAX_FORTRAN_DIMS)
	  error (_("Too many subscripts for F77 (%d Max)"), MAX_FORTRAN_DIMS);

	tmp_type = check_typedef (value_type (arg1));
	ndimensions = calc_f77_array_dims (type);

	if (nargs != ndimensions)
	  error (_("Wrong number of subscripts"));

	/* Now that we know we have a legal array subscript expression 
	   let us actually find out where this element exists in the array. */

	offset_item = 0;
	/* Take array indices left to right */
	for (i = 0; i < nargs; i++)
	  {
	    /* Evaluate each subscript, It must be a legal integer in F77 */
	    arg2 = evaluate_subexp_with_coercion (exp, pos, noside);

	    /* Fill in the subscript and array size arrays */

	    subscript_array[i] = value_as_long (arg2);
	  }

	/* Internal type of array is arranged right to left */
	for (i = 0; i < nargs; i++)
	  {
	    retcode = f77_get_dynamic_upperbound (tmp_type, &upper);
	    if (retcode == BOUND_FETCH_ERROR)
	      error (_("Cannot obtain dynamic upper bound"));

	    retcode = f77_get_dynamic_lowerbound (tmp_type, &lower);
	    if (retcode == BOUND_FETCH_ERROR)
	      error (_("Cannot obtain dynamic lower bound"));

	    array_size_array[nargs - i - 1] = upper - lower + 1;

	    /* Zero-normalize subscripts so that offsetting will work. */

	    subscript_array[nargs - i - 1] -= lower;

	    /* If we are at the bottom of a multidimensional 
	       array type then keep a ptr to the last ARRAY
	       type around for use when calling value_subscript()
	       below. This is done because we pretend to value_subscript
	       that we actually have a one-dimensional array 
	       of base element type that we apply a simple 
	       offset to. */

	    if (i < nargs - 1)
	      tmp_type = check_typedef (TYPE_TARGET_TYPE (tmp_type));
	  }

	/* Now let us calculate the offset for this item */

	offset_item = subscript_array[ndimensions - 1];

	for (i = ndimensions - 1; i > 0; --i)
	  offset_item =
	    array_size_array[i - 1] * offset_item + subscript_array[i - 1];

	/* Construct a value node with the value of the offset */

	arg2 = value_from_longest (builtin_type_f_integer, offset_item);

	/* Let us now play a dirty trick: we will take arg1 
	   which is a value node pointing to the topmost level
	   of the multidimensional array-set and pretend
	   that it is actually a array of the final element 
	   type, this will ensure that value_subscript()
	   returns the correct type value */

	deprecated_set_value_type (arg1, tmp_type);
	return value_ind (value_add (value_coerce_array (arg1), arg2));
      }

    case BINOP_LOGICAL_AND:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	{
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	  goto nosideret;
	}

      oldpos = *pos;
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, EVAL_AVOID_SIDE_EFFECTS);
      *pos = oldpos;

      if (binop_user_defined_p (op, arg1, arg2))
	{
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_logical_not (arg1);
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos,
				  (tem ? EVAL_SKIP : noside));
	  return value_from_longest (LA_BOOL_TYPE,
			     (LONGEST) (!tem && !value_logical_not (arg2)));
	}

    case BINOP_LOGICAL_OR:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	{
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	  goto nosideret;
	}

      oldpos = *pos;
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, EVAL_AVOID_SIDE_EFFECTS);
      *pos = oldpos;

      if (binop_user_defined_p (op, arg1, arg2))
	{
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_logical_not (arg1);
	  arg2 = evaluate_subexp (NULL_TYPE, exp, pos,
				  (!tem ? EVAL_SKIP : noside));
	  return value_from_longest (LA_BOOL_TYPE,
			     (LONGEST) (!tem || !value_logical_not (arg2)));
	}

    case BINOP_EQUAL:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_equal (arg1, arg2);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) tem);
	}

    case BINOP_NOTEQUAL:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_equal (arg1, arg2);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) ! tem);
	}

    case BINOP_LESS:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_less (arg1, arg2);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) tem);
	}

    case BINOP_GTR:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_less (arg2, arg1);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) tem);
	}

    case BINOP_GEQ:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_less (arg2, arg1) || value_equal (arg1, arg2);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) tem);
	}

    case BINOP_LEQ:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (value_type (arg1), exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (binop_user_defined_p (op, arg1, arg2))
	{
	  return value_x_binop (arg1, arg2, op, OP_NULL, noside);
	}
      else
	{
	  tem = value_less (arg1, arg2) || value_equal (arg1, arg2);
	  return value_from_longest (LA_BOOL_TYPE, (LONGEST) tem);
	}

    case BINOP_REPEAT:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      arg2 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      type = check_typedef (value_type (arg2));
      if (TYPE_CODE (type) != TYPE_CODE_INT)
	error (_("Non-integral right operand for \"@\" operator."));
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	{
	  return allocate_repeat_value (value_type (arg1),
				     longest_to_int (value_as_long (arg2)));
	}
      else
	return value_repeat (arg1, longest_to_int (value_as_long (arg2)));

    case BINOP_COMMA:
      evaluate_subexp (NULL_TYPE, exp, pos, noside);
      return evaluate_subexp (NULL_TYPE, exp, pos, noside);

    case UNOP_PLUS:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (unop_user_defined_p (op, arg1))
	return value_x_unop (arg1, op, noside);
      else
	return value_pos (arg1);
      
    case UNOP_NEG:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (unop_user_defined_p (op, arg1))
	return value_x_unop (arg1, op, noside);
      else
	return value_neg (arg1);

    case UNOP_COMPLEMENT:
      /* C++: check for and handle destructor names.  */
      op = exp->elts[*pos].opcode;

      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (unop_user_defined_p (UNOP_COMPLEMENT, arg1))
	return value_x_unop (arg1, UNOP_COMPLEMENT, noside);
      else
	return value_complement (arg1);

    case UNOP_LOGICAL_NOT:
      arg1 = evaluate_subexp (NULL_TYPE, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (unop_user_defined_p (op, arg1))
	return value_x_unop (arg1, op, noside);
      else
	return value_from_longest (LA_BOOL_TYPE,
				   (LONGEST) value_logical_not (arg1));

    case UNOP_IND:
      if (expect_type && TYPE_CODE (expect_type) == TYPE_CODE_PTR)
	expect_type = TYPE_TARGET_TYPE (check_typedef (expect_type));
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      type = check_typedef (value_type (arg1));
      if (TYPE_CODE (type) == TYPE_CODE_METHODPTR
	  || TYPE_CODE (type) == TYPE_CODE_MEMBERPTR)
	error (_("Attempt to dereference pointer to member without an object"));
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (unop_user_defined_p (op, arg1))
	return value_x_unop (arg1, op, noside);
      else if (noside == EVAL_AVOID_SIDE_EFFECTS)
	{
	  type = check_typedef (value_type (arg1));
	  if (TYPE_CODE (type) == TYPE_CODE_PTR
	      || TYPE_CODE (type) == TYPE_CODE_REF
	  /* In C you can dereference an array to get the 1st elt.  */
	      || TYPE_CODE (type) == TYPE_CODE_ARRAY
	    )
	    return value_zero (TYPE_TARGET_TYPE (type),
			       lval_memory);
	  else if (TYPE_CODE (type) == TYPE_CODE_INT)
	    /* GDB allows dereferencing an int.  */
	    return value_zero (builtin_type_int, lval_memory);
	  else
	    error (_("Attempt to take contents of a non-pointer value."));
	}
      return value_ind (arg1);

    case UNOP_ADDR:
      /* C++: check for and handle pointer to members.  */

      op = exp->elts[*pos].opcode;

      if (noside == EVAL_SKIP)
	{
	  evaluate_subexp (NULL_TYPE, exp, pos, EVAL_SKIP);
	  goto nosideret;
	}
      else
	{
	  struct value *retvalp = evaluate_subexp_for_address (exp, pos, noside);
	  /* If HP aCC object, use bias for pointers to members */
	  if (deprecated_hp_som_som_object_present
	      && TYPE_CODE (value_type (retvalp)) == TYPE_CODE_MEMBERPTR)
	    {
	      unsigned int *ptr = (unsigned int *) value_contents (retvalp);	/* forces evaluation */
	      *ptr |= 0x20000000;	/* set 29th bit */
	    }
	  return retvalp;
	}

    case UNOP_SIZEOF:
      if (noside == EVAL_SKIP)
	{
	  evaluate_subexp (NULL_TYPE, exp, pos, EVAL_SKIP);
	  goto nosideret;
	}
      return evaluate_subexp_for_sizeof (exp, pos);

    case UNOP_CAST:
      (*pos) += 2;
      type = exp->elts[pc + 1].type;
      arg1 = evaluate_subexp (type, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (type != value_type (arg1))
	arg1 = value_cast (type, arg1);
      return arg1;

    case UNOP_MEMVAL:
      (*pos) += 2;
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      if (noside == EVAL_SKIP)
	goto nosideret;
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	return value_zero (exp->elts[pc + 1].type, lval_memory);
      else
	return value_at_lazy (exp->elts[pc + 1].type,
			      value_as_address (arg1));

    case UNOP_PREINCREMENT:
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      else if (unop_user_defined_p (op, arg1))
	{
	  return value_x_unop (arg1, op, noside);
	}
      else
	{
	  arg2 = value_add (arg1, value_from_longest (builtin_type_char,
						      (LONGEST) 1));
	  return value_assign (arg1, arg2);
	}

    case UNOP_PREDECREMENT:
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      else if (unop_user_defined_p (op, arg1))
	{
	  return value_x_unop (arg1, op, noside);
	}
      else
	{
	  arg2 = value_sub (arg1, value_from_longest (builtin_type_char,
						      (LONGEST) 1));
	  return value_assign (arg1, arg2);
	}

    case UNOP_POSTINCREMENT:
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      else if (unop_user_defined_p (op, arg1))
	{
	  return value_x_unop (arg1, op, noside);
	}
      else
	{
	  arg2 = value_add (arg1, value_from_longest (builtin_type_char,
						      (LONGEST) 1));
	  value_assign (arg1, arg2);
	  return arg1;
	}

    case UNOP_POSTDECREMENT:
      arg1 = evaluate_subexp (expect_type, exp, pos, noside);
      if (noside == EVAL_SKIP || noside == EVAL_AVOID_SIDE_EFFECTS)
	return arg1;
      else if (unop_user_defined_p (op, arg1))
	{
	  return value_x_unop (arg1, op, noside);
	}
      else
	{
	  arg2 = value_sub (arg1, value_from_longest (builtin_type_char,
						      (LONGEST) 1));
	  value_assign (arg1, arg2);
	  return arg1;
	}

    case OP_THIS:
      (*pos) += 1;
      /* EMBARCADERO Local: begin self member access. */
      if (current_language->la_language == language_pascal)
        {
	  struct value *this_val;
	  this_val = value_of_local ("self", 0);
	  if (this_val)
	    return this_val;
	}
      /* EMBARCADERO Local: end self member access. */
      return value_of_local ("this", 1);

    /* APPLE LOCAL */
    case OP_OBJC_SELF:
      (*pos) += 1;
      return value_of_local ("self", 1);

    case OP_TYPE:
      error (_("Attempt to use a type name as an expression"));

    default:
      /* Removing this case and compiling with gcc -Wall reveals that
         a lot of cases are hitting this case.  Some of these should
         probably be removed from expression.h; others are legitimate
         expressions which are (apparently) not fully implemented.

         If there are any cases landing here which mean a user error,
         then they should be separate cases, with more descriptive
         error messages.  */

      error (_("\
GDB does not (yet) know how to evaluate that kind of expression"));
    }

nosideret:
  return value_from_longest (builtin_type_long, (LONGEST) 1);
}

/* Evaluate a subexpression of EXP, at index *POS,
   and return the address of that subexpression.
   Advance *POS over the subexpression.
   If the subexpression isn't an lvalue, get an error.
   NOSIDE may be EVAL_AVOID_SIDE_EFFECTS;
   then only the type of the result need be correct.  */

static struct value *
evaluate_subexp_for_address (struct expression *exp, int *pos,
			     enum noside noside)
{
  enum exp_opcode op;
  int pc;
  struct symbol *var;
  struct value *x;
  int tem;

  pc = (*pos);
  op = exp->elts[pc].opcode;

  switch (op)
    {
    case UNOP_IND:
      (*pos)++;
      x = evaluate_subexp (NULL_TYPE, exp, pos, noside);

      /* We can't optimize out "&*" if there's a user-defined operator*.  */
      if (unop_user_defined_p (op, x))
	{
	  x = value_x_unop (x, op, noside);
	  goto default_case_after_eval;
	}

      return coerce_array (x);

    case UNOP_MEMVAL:
      (*pos) += 3;
      return value_cast (lookup_pointer_type (exp->elts[pc + 1].type),
			 evaluate_subexp (NULL_TYPE, exp, pos, noside));

    case OP_VAR_VALUE:
      var = exp->elts[pc + 2].symbol;

      /* C++: The "address" of a reference should yield the address
       * of the object pointed to. Let value_addr() deal with it. */
      if (TYPE_CODE (SYMBOL_TYPE (var)) == TYPE_CODE_REF)
	goto default_case;

      (*pos) += 4;
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	{
	  struct type *type =
	  lookup_pointer_type (SYMBOL_TYPE (var));
	  enum address_class sym_class = SYMBOL_CLASS (var);

	  if (sym_class == LOC_CONST
	      || sym_class == LOC_CONST_BYTES
	      || sym_class == LOC_REGISTER
	      || sym_class == LOC_REGPARM)
	    error (_("Attempt to take address of register or constant."));

	  return
	    value_zero (type, not_lval);
	}
      else
	return
	  locate_var_value
	  (var,
	   block_innermost_frame (exp->elts[pc + 1].block));

    case OP_SCOPE:
      tem = longest_to_int (exp->elts[pc + 2].longconst);
      (*pos) += 5 + BYTES_TO_EXP_ELEM (tem + 1);
      x = value_aggregate_elt (exp->elts[pc + 1].type,
			       &exp->elts[pc + 3].string,
			       1, noside);
      if (x == NULL)
	error (_("There is no field named %s"), &exp->elts[pc + 3].string);
      return x;

    default:
    default_case:
      x = evaluate_subexp (NULL_TYPE, exp, pos, noside);
    default_case_after_eval:
      if (noside == EVAL_AVOID_SIDE_EFFECTS)
	{
	  struct type *type = check_typedef (value_type (x));

	  if (VALUE_LVAL (x) == lval_memory)
	    return value_zero (lookup_pointer_type (value_type (x)),
			       not_lval);
	  else if (TYPE_CODE (type) == TYPE_CODE_REF)
	    return value_zero (lookup_pointer_type (TYPE_TARGET_TYPE (type)),
			       not_lval);
	  else
	    error (_("Attempt to take address of non-lval"));
	}
      return value_addr (x);
    }
}

/* Evaluate like `evaluate_subexp' except coercing arrays to pointers.
   When used in contexts where arrays will be coerced anyway, this is
   equivalent to `evaluate_subexp' but much faster because it avoids
   actually fetching array contents (perhaps obsolete now that we have
   value_lazy()).

   Note that we currently only do the coercion for C expressions, where
   arrays are zero based and the coercion is correct.  For other languages,
   with nonzero based arrays, coercion loses.  Use CAST_IS_CONVERSION
   to decide if coercion is appropriate.

   APPLE LOCAL: If this is a vector type, don't coerce it to a
   pointer, as then we would lose the 'stride' attribute.

 */

struct value *
evaluate_subexp_with_coercion (struct expression *exp,
			       int *pos, enum noside noside)
{
  enum exp_opcode op;
  int pc;
  struct value *val;
  struct symbol *var;

  pc = (*pos);
  op = exp->elts[pc].opcode;

  switch (op)
    {
    case OP_VAR_VALUE:
      var = exp->elts[pc + 2].symbol;
      if (TYPE_CODE (check_typedef (SYMBOL_TYPE (var))) == TYPE_CODE_ARRAY
	  /* APPLE LOCAL: Don't coerce to pointer if it's a vector type. */
	  && (! TYPE_FLAGS (check_typedef (SYMBOL_TYPE (var))) & TYPE_FLAG_VECTOR)
	  && CAST_IS_CONVERSION)
	{
	  (*pos) += 4;
	  val =
	    locate_var_value
	    (var, block_innermost_frame (exp->elts[pc + 1].block));
	  return value_cast (lookup_pointer_type (TYPE_TARGET_TYPE (check_typedef (SYMBOL_TYPE (var)))),
			     val);
	}
      /* FALLTHROUGH */

    default:
      return evaluate_subexp (NULL_TYPE, exp, pos, noside);
    }
}

/* Evaluate a subexpression of EXP, at index *POS,
   and return a value for the size of that subexpression.
   Advance *POS over the subexpression.  */

static struct value *
evaluate_subexp_for_sizeof (struct expression *exp, int *pos)
{
  enum exp_opcode op;
  int pc;
  struct type *type;
  struct value *val;

  pc = (*pos);
  op = exp->elts[pc].opcode;

  switch (op)
    {
      /* This case is handled specially
         so that we avoid creating a value for the result type.
         If the result type is very big, it's desirable not to
         create a value unnecessarily.  */
    case UNOP_IND:
      (*pos)++;
      val = evaluate_subexp (NULL_TYPE, exp, pos, EVAL_AVOID_SIDE_EFFECTS);
      type = check_typedef (value_type (val));
      if (TYPE_CODE (type) != TYPE_CODE_PTR
	  && TYPE_CODE (type) != TYPE_CODE_REF
	  && TYPE_CODE (type) != TYPE_CODE_ARRAY)
	error (_("Attempt to take contents of a non-pointer value."));
      type = check_typedef (TYPE_TARGET_TYPE (type));
      return value_from_longest (builtin_type_int, (LONGEST)
				 TYPE_LENGTH (type));

    case UNOP_MEMVAL:
      (*pos) += 3;
      type = check_typedef (exp->elts[pc + 1].type);
      return value_from_longest (builtin_type_int,
				 (LONGEST) TYPE_LENGTH (type));

    case OP_VAR_VALUE:
      (*pos) += 4;
      type = check_typedef (SYMBOL_TYPE (exp->elts[pc + 2].symbol));
      return
	value_from_longest (builtin_type_int, (LONGEST) TYPE_LENGTH (type));

    default:
      val = evaluate_subexp (NULL_TYPE, exp, pos, EVAL_AVOID_SIDE_EFFECTS);
      return value_from_longest (builtin_type_int,
				 (LONGEST) TYPE_LENGTH (value_type (val)));
    }
}

/* Parse a type expression in the string [P..P+LENGTH). */

struct type *
parse_and_eval_type (char *p, int length)
{
  char *tmp = (char *) alloca (length + 4);
  struct expression *expr;
  tmp[0] = '(';
  memcpy (tmp + 1, p, length);
  tmp[length + 1] = ')';
  tmp[length + 2] = '0';
  tmp[length + 3] = '\0';
  /* APPLE LOCAL initialize innermost_block  */
  innermost_block = NULL;
  expr = parse_expression (tmp);
  if (expr->elts[0].opcode != UNOP_CAST)
    error (_("Internal error in eval_type."));
  return expr->elts[1].type;
}

int
calc_f77_array_dims (struct type *array_type)
{
  int ndimen = 1;
  struct type *tmp_type;

  if ((TYPE_CODE (array_type) != TYPE_CODE_ARRAY))
    error (_("Can't get dimensions for a non-array type"));

  tmp_type = array_type;

  while ((tmp_type = TYPE_TARGET_TYPE (tmp_type)))
    {
      if (TYPE_CODE (tmp_type) == TYPE_CODE_ARRAY)
	++ndimen;
    }
  return ndimen;
}
