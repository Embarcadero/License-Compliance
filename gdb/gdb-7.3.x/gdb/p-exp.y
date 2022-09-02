/* YACC parser for Pascal expressions, for GDB.
   Copyright (C) 2000, 2006, 2007, 2008, 2009, 2010, 2011
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

/* This file is derived from c-exp.y */

/* Parse a Pascal expression from text in a string,
   and return the result as a  struct expression  pointer.
   That structure contains arithmetic operations in reverse polish,
   with constants represented by operations that are followed by special data.
   See expression.h for the details of the format.
   What is important here is that it can be built up sequentially
   during the process of parsing; the lower levels of the tree always
   come first in the result.

   Note that malloc's and realloc's in this file are transformed to
   xmalloc and xrealloc respectively by the same sed command in the
   makefile that remaps any other malloc/realloc inserted by the parser
   generator.  Doing this with #defines and trying to control the interaction
   with include files (<malloc.h> and <stdlib.h> for example) just became
   too messy, particularly when such includes can be inserted at random
   times by the parser generator.  */

/* Known bugs or limitations:
    - pascal string operations are not supported at all.
    - there are some problems with boolean types.
    - Pascal type hexadecimal constants are not supported
      because they conflict with the internal variables format.
   Probably also lots of other problems, less well defined PM.  */
%{

#include "defs.h"
#include "gdb_string.h"
#include <ctype.h>
#include "expression.h"
#include "value.h"
#include "parser-defs.h"
#include "language.h"
#include "p-lang.h"
#include "bfd.h" /* Required by objfiles.h.  */
#include "symfile.h" /* Required by objfiles.h.  */
#include "objfiles.h" /* For have_full_symbols and have_partial_symbols.  */
#include "block.h"
#include "cp-support.h"
#include "gdb_assert.h"

#define parse_type builtin_type (parse_gdbarch)

/* Remap normal yacc parser interface names (yyparse, yylex, yyerror, etc),
   as well as gratuitiously global symbol names, so we can have multiple
   yacc generated parsers in gdb.  Note that these are only the variables
   produced by yacc.  If other parser generators (bison, byacc, etc) produce
   additional global names that conflict at link time, then those parser
   generators need to be fixed instead of adding those names to this list.  */

#define	yymaxdepth pascal_maxdepth
#define	yyparse	pascal_parse
#define	yylex	pascal_lex
#define	yyerror	pascal_error
#define	yylval	pascal_lval
#define	yychar	pascal_char
#define	yydebug	pascal_debug
#define	yypact	pascal_pact
#define	yyr1	pascal_r1
#define	yyr2	pascal_r2
#define	yydef	pascal_def
#define	yychk	pascal_chk
#define	yypgo	pascal_pgo
#define	yyact	pascal_act
#define	yyexca	pascal_exca
#define yyerrflag pascal_errflag
#define yynerrs	pascal_nerrs
#define	yyps	pascal_ps
#define	yypv	pascal_pv
#define	yys	pascal_s
#define	yy_yys	pascal_yys
#define	yystate	pascal_state
#define	yytmp	pascal_tmp
#define	yyv	pascal_v
#define	yy_yyv	pascal_yyv
#define	yyval	pascal_val
#define	yylloc	pascal_lloc
#define yyreds	pascal_reds		/* With YYDEBUG defined */
#define yytoks	pascal_toks		/* With YYDEBUG defined */
#define yyname	pascal_name		/* With YYDEBUG defined */
#define yyrule	pascal_rule		/* With YYDEBUG defined */
#define yylhs	pascal_yylhs
#define yylen	pascal_yylen
#define yydefred pascal_yydefred
#define yydgoto	pascal_yydgoto
#define yysindex pascal_yysindex
#define yyrindex pascal_yyrindex
#define yygindex pascal_yygindex
#define yytable	 pascal_yytable
#define yycheck	 pascal_yycheck

/* Define YYDEBUG to enable debugging.  */
#ifndef YYDEBUG
/* EMBARCADERO Local turn parser debugging off by default */
#define	YYDEBUG 0		/* Default to yydebug support */
#endif

#define YYFPRINTF parser_fprintf

int yyparse (void);

static int yylex (void);

void yyerror (char *);

static char * uptok (char *, int);

/* EMBARCADERO Local begin parser debugging */
#if YYDEBUG == 1
#define DUMP_CURRENT_TYPE(str) dump_current_type (str)
#define DUMP_TYPE(str, type) dump_type (str, type)
#define DUMP_STRING(str, str2) dump_string (str, str2)
#define DUMP_STOKEN(str, stok) dump_stoken (str, stok)
#define DUMP_TTYPE(str, tsym) dump_ttype (str, tsym)
#define DUMP_SYMTOKEN(str, ssym) dump_symtoken (str, ssym)
static void dump_current_type (const char *str);
static void dump_type (const char *str, struct type *type);
static void dump_string (const char *str, const char *str2);
static void dump_stoken (const char *str, struct stoken *stok);
static void dump_ttype (const char *str, struct ttype *tsym);
static void dump_symtoken (const char *str, struct symtoken *ssym);
#else /* YYDEBUG */
#define DUMP_CURRENT_TYPE(str)
#define DUMP_TYPE(str, type)
#define DUMP_STRING(str, str2)
#define DUMP_STOKEN(str, tok)
#define DUMP_TTYPE(str, type)
#define DUMP_SYMTOKEN(str, ssym)
#endif /* YYDEBUG */
/* EMBARCADERO Local end parser debugging */
%}

/* Although the yacc "value" of an expression is not used,
   since the result is stored in the structure being created,
   other node types do have values.  */

%union
  {
    LONGEST lval;
    struct {
      LONGEST val;
      struct type *type;
    } typed_val_int;
    struct {
      DOUBLEST dval;
      struct type *type;
    } typed_val_float;
    struct symbol *sym;
    struct type *tval;
    struct stoken sval;
    struct ttype tsym;
    struct symtoken ssym;
    int voidval;
    struct block *bval;
    enum exp_opcode opcode;
    struct internalvar *ivar;

    struct type **tvec;
    int *ivec;
  }

%{
/* YYSTYPE gets defined by %union */
static int parse_number (char *, int, int, YYSTYPE *);

static struct type *current_type;
static struct internalvar *intvar;
static int leftdiv_is_integer;
static void push_current_type (void);
static void pop_current_type (void);
static int search_field;
static struct fn_field *current_method;
static struct prop_field *current_property;

/* EMBARCADERO LOCAL begin Delphi units */
/* This is set if the previously-returned token was a structure
   namespace operator '.'.  Note: we make saw_structop global so
   we can test for it in parsing rules. */
static int last_was_structop;
static int saw_structop;
/* EMBARCADERO LOCAL end Delphi units */

/* EMBARCADERO LOCAL begin string literals */
typedef uint16_t chartype;
const int charsize = 2;
/* EMBARCADERO LOCAL end string literals */
%}

%type <voidval> exp exp1 type_exp start normal_start variable qualified_name
%type <tval> type typebase
/* %type <bval> block */

/* Fancy type parsing.  */
%type <tval> ptype

%token <typed_val_int> INT
%token <typed_val_float> FLOAT

/* Both NAME and TYPENAME tokens represent symbols in the input,
   and both convey their data as strings.
   But a TYPENAME is a string that happens to be defined as a typedef
   or builtin type name (such as int or char)
   and a NAME is any other symbol.
   Contexts where this distinction is not important can use the
   nonterminal "name", which matches either NAME or TYPENAME.  */

%token <sval> STRING
%token <sval> IDENT
%token <voidval> COMPLETE
%token <ssym> NAME /* BLOCKNAME defined below to give it higher precedence.  */
%token <tsym> TYPENAME
%type <sval> ident
%type <sval> name
%type <ssym> name_not_typename

/* A NAME_OR_INT is a symbol which is not known in the symbol table,
   but which would parse as a valid number in the current input radix.
   E.g. "c" when input_radix==16.  Depending on the parse, it will be
   turned into a name or into a number.  */

%token <ssym> NAME_OR_INT

%token STRUCT CLASS SIZEOF COLONCOLON
%token ERROR

/* Special type cases, put in to allow the parser to distinguish different
   legal basetypes.  */

%token <voidval> VARIABLE


/* Object pascal */
%token THIS
%token <lval> TRUEKEYWORD FALSEKEYWORD

%left ','
%left ABOVE_COMMA
%right ASSIGN
%left NOT
%left OR
%left XOR
%left ANDAND
%left '=' NOTEQUAL
%left '<' '>' LEQ GEQ
%left LSH RSH DIV MOD
%left '@'
%left '+' '-'
%left '*' '/'
%right UNARY INCREMENT DECREMENT
%right ARROW '.' '[' '('
%left '^'
%token <ssym> BLOCKNAME
%type <bval> block
%left COLONCOLON


%%

start   :	{ current_type = NULL;
		  DUMP_CURRENT_TYPE ("start");
		  current_method = 0;
		  current_property = 0;
		  intvar = NULL;
		  search_field = 0;
		  leftdiv_is_integer = 0;
#if YYDEBUG == 1
		  pascal_debug = 1;
#endif
		}
		normal_start {}
	;

normal_start	:
		exp1
	|	type_exp
	;

type_exp:	type
			{ write_exp_elt_opcode(OP_TYPE);
			  write_exp_elt_type($1);
			  write_exp_elt_opcode(OP_TYPE);
			  current_type = $1;
			  DUMP_CURRENT_TYPE ("type_exp:type");
			} ;

/* Expressions, including the comma operator.  */
exp1	:	exp
	|	exp1 ',' exp
			{ write_exp_elt_opcode (BINOP_COMMA); }
	;

/* Expressions, not including the comma operator.  */
exp	:	exp '^'   %prec UNARY
			{ write_exp_elt_opcode (UNOP_IND);
			  if (current_type)
			    current_type = TYPE_TARGET_TYPE (current_type); }
	;

exp	:	'@' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_ADDR);
			  if (current_type)
			    current_type = TYPE_POINTER_TYPE (current_type); }
	;

exp	:	'-' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_NEG); }
	;

exp	:	NOT exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_LOGICAL_NOT); }
	;

exp	:	INCREMENT '(' exp ')'   %prec UNARY
			{ write_exp_elt_opcode (UNOP_PREINCREMENT); }
	;

exp	:	DECREMENT  '(' exp ')'   %prec UNARY
			{ write_exp_elt_opcode (UNOP_PREDECREMENT); }
	;

//field_exp	:	exp '.'	%prec UNARY
//			{ search_field = 1; }
//	;
//
//exp	:	field_exp FIELDNAME
//			{ write_exp_elt_opcode (STRUCTOP_STRUCT);
//			  write_exp_string ($2);
//			  write_exp_elt_opcode (STRUCTOP_STRUCT);
//			  search_field = 0;
//			  if (current_type)
//			    {
//			      while (TYPE_CODE (current_type)
//				     == TYPE_CODE_PTR)
//			        /* Dereference the object. */ 
//				current_type =
//				  TYPE_TARGET_TYPE (current_type);
//			      /* Reset the object to ... what's name.ptr??? */ 
//			      current_type = lookup_struct_elt_type (
//				current_type, $2.ptr, 0);
//			    }
//			 }
//	;
//
//
//exp	:	field_exp name
//			{ mark_struct_expression ();
//			  write_exp_elt_opcode (STRUCTOP_STRUCT);
//			  write_exp_string ($2);
//			  write_exp_elt_opcode (STRUCTOP_STRUCT);
//			  search_field = 0;
//			  if (current_type)
//			    {
//			      while (TYPE_CODE (current_type)
//				     == TYPE_CODE_PTR)
//				current_type =
//				  TYPE_TARGET_TYPE (current_type);
//			      current_type = lookup_struct_elt_type (
//				current_type, $2.ptr, 0);
//			    }
//			}
//	;
//
//exp	:	field_exp COMPLETE
//			{ struct stoken s;
//			  mark_struct_expression ();
//			  write_exp_elt_opcode (STRUCTOP_STRUCT);
//			  s.ptr = "";
//			  s.length = 0;
//			  write_exp_string (s);
//			  write_exp_elt_opcode (STRUCTOP_STRUCT); }
//	;

/* EMBARCADERO Local: begin properties and method calls. */
exp	:	exp '.' ident %prec UNARY
			{ current_method = 0;
			  current_property = 0;
			  DUMP_CURRENT_TYPE ("exp:exp'.'ident");
			  if (current_type)
			    { while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				{ /* Dereference the object. */ 
				  current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("exp:exp'.'ident#1");
				}

			      /* Special case: evaluate "object.method"
				 as a function call. */
			      current_method = lookup_struct_elt_fn_field (
				current_type, $3.ptr, 0);
			      if (!current_method)
			        current_property = lookup_struct_elt_prop_field (
				  current_type, $3.ptr);
			    }
			  /* If property read is just a field, use that field.
			     FIXME: need to support writing! */
			  if (current_property &&
				  PROP_FIELD_READ_NAME(*current_property) &&
				  !PROP_FIELD_GETTER(*current_property))
			    { char* prop_read_name =
				    PROP_FIELD_READ_NAME(*current_property);
			      $3.ptr = prop_read_name;
			      $3.length = strlen(prop_read_name);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
                              /* Reset the type to the type of the property. */
                              current_type = current_property->type;
			      DUMP_CURRENT_TYPE ("exp:exp'.'ident#2");
                              current_property = 0;
			    }
			  /* If property read is a getter, use that method.
			     FIXME: need to support writing! */
			  else if (current_property &&
				   PROP_FIELD_READ_NAME(*current_property) &&
				   PROP_FIELD_GETTER(*current_property))
			    { char* prop_read_name =
				    PROP_FIELD_READ_NAME(*current_property);
			      $3.ptr = prop_read_name;
			      $3.length = strlen(prop_read_name);
			      current_method = lookup_struct_elt_fn_field (
				current_type, prop_read_name, 0);
                              current_property = 0;
			      goto do_method;
			    }
			  else if (current_property)
			    { error (_("Property \"%s\" not readable."),
				     $3.ptr);
			      current_property = 0;
			    }
			  else if (current_method)
			    {
			    do_method:
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      start_arglist ();
			      write_exp_elt_opcode (OP_FUNCALL);
			      write_exp_elt_longcst ((LONGEST) end_arglist ());
			      write_exp_elt_opcode (OP_FUNCALL); 
                              /* Reset the type to the return type of the method. */
			      if (current_method)
			      { current_type = TYPE_TARGET_TYPE (current_method->type);
				DUMP_CURRENT_TYPE ("exp:exp'.'ident#3");
			      }
			      current_method = 0;
			    }
			  else
			    { write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
                              /* Reset the type to the type of the field. */
			      if (current_type)
			      { current_type = lookup_struct_elt_type (
				  current_type, $3.ptr, 0);
				DUMP_CURRENT_TYPE ("exp:exp'.'ident#4");
			      }
			    }
                        }
	;

exp	:	exp '.' ident '('
			{ DUMP_CURRENT_TYPE ("exp:exp'.'ident'('arglist')'");
			  if (current_type)
			    { while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				{ /* Dereference the object. */ 
				  current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("exp:exp'.'ident'('arglist')'#1");
				}
			    }
			  /* This is to save the value of arglist_len
			     being accumulated by an outer function call.  */
			  push_current_type ();
			  start_arglist (); 
                          write_exp_elt_opcode (STRUCTOP_STRUCT);
                          write_exp_string ($3);
                          write_exp_elt_opcode (STRUCTOP_STRUCT);
			}
		arglist ')'	%prec ARROW
			{ write_exp_elt_opcode (OP_FUNCALL);
			  write_exp_elt_longcst ((LONGEST) end_arglist ());
			  write_exp_elt_opcode (OP_FUNCALL); 
			  pop_current_type (); 
			  if (current_type)
			  { current_type = TYPE_TARGET_TYPE (current_type);
			    DUMP_CURRENT_TYPE ("exp:exp'.'ident'('arglist')'#2");
			  }
			}
	;
/* EMBARCADERO Local: end properties and method calls. */

/* EMBARCADERO LOCAL: begin support of Multi-dimensional arrays. 
   Pascal addressing style. */
exp	:	exp '['
			{ push_current_type();
			  start_arglist();
			}
		arglist ']'
			{ if (arglist_len > 1) 
			    { write_exp_elt_opcode (OP_PASCAL_UNDETERMINED_ARGLIST);
			      write_exp_elt_longcst ((LONGEST) end_arglist ());
			      write_exp_elt_opcode (OP_PASCAL_UNDETERMINED_ARGLIST);
			      pop_current_type ();
			      if (current_type)
				{ current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("exp:exp'['arglist']'");
				}
			    } 
			  else 
			    { pop_current_type();
			      write_exp_elt_opcode (BINOP_SUBSCRIPT); 
			      if (current_type)
				{ current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("exp:exp'['arglist']'#2");
				}
			    }
			}
	;
/* EMBARCADERO LOCAL: end of support of Multi-dimensional arrays */ 

exp	:	exp '('
			/* This is to save the value of arglist_len
			   being accumulated by an outer function call.  */
			{ push_current_type ();
			  start_arglist (); }
		arglist ')'	%prec ARROW
			{
			  /* EMBARCADERO Local: method call support. */
			  /* "myobject.method" will actually call
			     myobject.method(), so check current_method so we
			     don't accidently call (myobject.method())().  */
			  if (!current_method)
			    { write_exp_elt_opcode (OP_FUNCALL);
			      write_exp_elt_longcst ((LONGEST) end_arglist ());
			      write_exp_elt_opcode (OP_FUNCALL); 
			    }
			  pop_current_type ();
			  if (current_type)
			  { current_type = TYPE_TARGET_TYPE (current_type);
			    DUMP_CURRENT_TYPE ("exp:exp'('arglist')'");
			  }
			}
	;

arglist	:
	;

arglist	:	exp
			{ arglist_len = 1; }
	;

arglist	:	arglist ',' exp   %prec ABOVE_COMMA
			{ arglist_len++; }
	;


exp	:	type '(' exp ')' %prec UNARY
			{ if (current_type)
			    {
			      /* Allow automatic dereference of classes.  */
			      if ((TYPE_CODE (current_type) == TYPE_CODE_PTR)
				  && (TYPE_CODE (TYPE_TARGET_TYPE (current_type)) == TYPE_CODE_CLASS)
				  && (TYPE_CODE ($1) == TYPE_CODE_CLASS))
				write_exp_elt_opcode (UNOP_IND);
			    }
			  write_exp_elt_opcode (UNOP_CAST);
			  write_exp_elt_type ($1);
			  write_exp_elt_opcode (UNOP_CAST);
			  current_type = $1;
			  DUMP_CURRENT_TYPE ("exp:type'('exp')'");
			}
	;

exp	:	'(' exp1 ')'
			{ }
	;

/* Binary operators in order of decreasing precedence.  */

exp	:	exp '*' exp
			{ write_exp_elt_opcode (BINOP_MUL); }
	;

exp	:	exp '/' {
			  if (current_type && is_integral_type (current_type))
			    leftdiv_is_integer = 1;
			}
		exp
			{
			  if (leftdiv_is_integer && current_type
			      && is_integral_type (current_type))
			    {
			      write_exp_elt_opcode (UNOP_CAST);
			      write_exp_elt_type (parse_type->builtin_long_double);
			      current_type = parse_type->builtin_long_double;
			      write_exp_elt_opcode (UNOP_CAST);
			      leftdiv_is_integer = 0;
			    }

			  write_exp_elt_opcode (BINOP_DIV);
			}
	;

exp	:	exp DIV exp
			{ write_exp_elt_opcode (BINOP_INTDIV); }
	;

exp	:	exp MOD exp
			{ write_exp_elt_opcode (BINOP_REM); }
	;

exp	:	exp '+' exp
			{ write_exp_elt_opcode (BINOP_ADD); }
	;

exp	:	exp '-' exp
			{ write_exp_elt_opcode (BINOP_SUB); }
	;

exp	:	exp LSH exp
			{ write_exp_elt_opcode (BINOP_LSH); }
	;

exp	:	exp RSH exp
			{ write_exp_elt_opcode (BINOP_RSH); }
	;

exp	:	exp '=' exp
			{ write_exp_elt_opcode (BINOP_EQUAL);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp NOTEQUAL exp
			{ write_exp_elt_opcode (BINOP_NOTEQUAL);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp LEQ exp
			{ write_exp_elt_opcode (BINOP_LEQ);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp GEQ exp
			{ write_exp_elt_opcode (BINOP_GEQ);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp '<' exp
			{ write_exp_elt_opcode (BINOP_LESS);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp '>' exp
			{ write_exp_elt_opcode (BINOP_GTR);
			  current_type = parse_type->builtin_bool;
			}
	;

exp	:	exp ANDAND exp
			{ write_exp_elt_opcode (BINOP_BITWISE_AND); }
	;

exp	:	exp XOR exp
			{ write_exp_elt_opcode (BINOP_BITWISE_XOR); }
	;

exp	:	exp OR exp
			{ write_exp_elt_opcode (BINOP_BITWISE_IOR); }
	;

exp	:	exp ASSIGN exp
			{ write_exp_elt_opcode (BINOP_ASSIGN); }
	;

exp	:	TRUEKEYWORD
			{ write_exp_elt_opcode (OP_BOOL);
			  write_exp_elt_longcst ((LONGEST) $1);
			  current_type = parse_type->builtin_bool;
			  write_exp_elt_opcode (OP_BOOL); }
	;

exp	:	FALSEKEYWORD
			{ write_exp_elt_opcode (OP_BOOL);
			  write_exp_elt_longcst ((LONGEST) $1);
			  current_type = parse_type->builtin_bool;
			  write_exp_elt_opcode (OP_BOOL); }
	;

exp	:	INT
			{ write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type ($1.type);
			  current_type = $1.type;
			  write_exp_elt_longcst ((LONGEST)($1.val));
			  write_exp_elt_opcode (OP_LONG); }
	;

exp	:	NAME_OR_INT
			{ YYSTYPE val;
			  parse_number ($1.stoken.ptr,
					$1.stoken.length, 0, &val);
			  write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (val.typed_val_int.type);
			  current_type = val.typed_val_int.type;
			  DUMP_CURRENT_TYPE ("exp:NAME_OR_INT");
			  write_exp_elt_longcst ((LONGEST)
						 val.typed_val_int.val);
			  write_exp_elt_opcode (OP_LONG);
			}
	;


exp	:	FLOAT
			{ write_exp_elt_opcode (OP_DOUBLE);
			  write_exp_elt_type ($1.type);
			  current_type = $1.type;
			  write_exp_elt_dblcst ($1.dval);
			  write_exp_elt_opcode (OP_DOUBLE); }
	;

exp	:	variable
	;

exp	:	VARIABLE
			/* Already written by write_dollar_variable.
			   Handle current_type.  */
 			{ if (intvar) {
			    struct value * val, * mark;

			     mark = value_mark ();
 			     val = value_of_internalvar (parse_gdbarch,
 							 intvar);
 			     current_type = value_type (val);
			     DUMP_CURRENT_TYPE ("exp:VARIABLE");
			     value_release_to_mark (mark);
 			   }
 			}
 	;

exp	:	SIZEOF '(' type ')'	%prec UNARY
			{ write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (parse_type->builtin_int);
			  CHECK_TYPEDEF ($3);
			  write_exp_elt_longcst ((LONGEST) TYPE_LENGTH ($3));
			  write_exp_elt_opcode (OP_LONG); }
	;

exp	:	SIZEOF  '(' exp ')'      %prec UNARY
			{ write_exp_elt_opcode (UNOP_SIZEOF); }

exp	:	STRING
			  /* EMBARCADERO LOCAL Delphi strings */
			{ /* Delphi strings are converted into array constants
			     with an explicit null byte added at the end.  Thus
			     the array upper bound is the string length.
			     There is no such thing as a completely empty
			     string.  */
			  chartype *sp = (chartype*)$1.ptr;
			  int count = $1.length/charsize;
			  int i;
			  for (i = 0; i < count; i++)
			    {
			      write_exp_elt_opcode (OP_LONG);
			      /* EMBARCADERO LOCAL Delphi strings */
			      /* was: write_exp_elt_type (parse_type->builtin_char); */
			      write_exp_elt_type (pascal_char_type (parse_gdbarch));
			      write_exp_elt_longcst (((LONGEST)sp[i])&0xffff);
			      write_exp_elt_opcode (OP_LONG);
			    }
			  write_exp_elt_opcode (OP_LONG);
			  /* EMBARCADERO LOCAL Delphi strings */
			  /* was: write_exp_elt_type (parse_type->builtin_char); */
			  write_exp_elt_type (pascal_char_type (parse_gdbarch));
			  write_exp_elt_longcst ((LONGEST)'\0');
			  write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_opcode (OP_ARRAY);
			  write_exp_elt_longcst ((LONGEST) 0);
			  write_exp_elt_longcst ((LONGEST) (count));
			  write_exp_elt_opcode (OP_ARRAY); }
	;

/* Object pascal  */
exp	:	THIS
			{
			  struct value * this_val;
			  struct type * this_type;
			  write_exp_elt_opcode (OP_THIS);
			  write_exp_elt_opcode (OP_THIS);
			  /* We need type of this.  */
			  this_val = value_of_this (0);
			  if (this_val)
			    this_type = value_type (this_val);
			  else
			    this_type = NULL;
			  if (this_type)
			    {
			      if (TYPE_CODE (this_type) == TYPE_CODE_PTR)
				{
				  this_type = TYPE_TARGET_TYPE (this_type);
				  write_exp_elt_opcode (UNOP_IND);
				}
			    }

			  current_type = this_type;
			  DUMP_CURRENT_TYPE ("exp:THIS");
			}
	;

/* end of object pascal.  */

block	:	BLOCKNAME
			{
			  if ($1.sym != 0)
			      $$ = SYMBOL_BLOCK_VALUE ($1.sym);
			  else
			    {
			      struct symtab *tem =
				  lookup_symtab (copy_name ($1.stoken));
			      if (tem)
				$$ = BLOCKVECTOR_BLOCK (BLOCKVECTOR (tem),
							STATIC_BLOCK);
			      else
				error (_("No file or function \"%s\"."),
				       copy_name ($1.stoken));
			    }
			}
	;

block	:	block COLONCOLON name
			{ struct symbol *tem
			    = lookup_symbol (copy_name ($3), $1,
					     VAR_DOMAIN, (int *) NULL);
			  if (!tem || SYMBOL_CLASS (tem) != LOC_BLOCK)
			    error (_("No function \"%s\" in specified context."),
				   copy_name ($3));
			  $$ = SYMBOL_BLOCK_VALUE (tem); }
	;

variable:	block COLONCOLON name
			{ struct symbol *sym;
			  sym = lookup_symbol (copy_name ($3), $1,
					       VAR_DOMAIN, (int *) NULL);
			  if (sym == 0)
			    error (_("No symbol \"%s\" in specified context."),
				   copy_name ($3));

			  write_exp_elt_opcode (OP_VAR_VALUE);
			  /* block_found is set by lookup_symbol.  */
			  write_exp_elt_block (block_found);
			  write_exp_elt_sym (sym);
			  write_exp_elt_opcode (OP_VAR_VALUE); }
	;

qualified_name:	typebase COLONCOLON name 
                | typebase '.' name
			{
			  struct type *type = $1;
			  DUMP_TYPE ("qualified_name:typebase'.'name#0", type);
			  DUMP_CURRENT_TYPE ("qualified_name:typebase'.'name");
			  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
			      && TYPE_CODE (type) != TYPE_CODE_UNION
			      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
			    error ("`%s' is not defined as an aggregate type.",
				   TYPE_NAME (type));

			  write_exp_elt_opcode (OP_SCOPE);
			  write_exp_elt_type (type);
			  write_exp_string ($3);
			  write_exp_elt_opcode (OP_SCOPE);
			  DUMP_CURRENT_TYPE ("qualified_name:typebase'.'name#2");
			  DUMP_TYPE ("qualified_name:typebase'.'name#3", $1);
			}
	;

variable:	qualified_name
	|	COLONCOLON name
			{
			  char *name = copy_name ($2);
			  struct symbol *sym;
			  struct minimal_symbol *msymbol;

			  sym =
			    lookup_symbol (name, (const struct block *) NULL,
					   VAR_DOMAIN, (int *) NULL);
			  if (sym)
			    {
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      break;
			    }

			  msymbol = lookup_minimal_symbol (name, NULL, NULL);
			  if (msymbol != NULL)
			    write_exp_msymbol (msymbol);
			  else if (!have_full_symbols ()
				   && !have_partial_symbols ())
			    error (_("No symbol table is loaded.  "
				   "Use the \"file\" command."));
			  else
			    error (_("No symbol \"%s\" in current context."),
				   name);
			}
	;

variable:	name_not_typename
			{ struct symbol *sym = $1.sym;

			  if (sym)
			    {
			      if (symbol_read_needs_frame (sym))
				{
				  if (innermost_block == 0
				      || contained_in (block_found,
						       innermost_block))
				    innermost_block = block_found;
				}

			      write_exp_elt_opcode (OP_VAR_VALUE);
			      /* We want to use the selected frame, not
				 another more inner frame which happens to
				 be in the same block.  */
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      current_type = sym->type;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename");
			    }
			  /* Is is a field of 'this'?  */
			  /* EMBARCADERO LOCAL: nested functions */
			  else if ($1.is_a_field_of_this == ifk_this)
			    {
			      struct value * this_val;
			      /* Object pascal: it hangs off of `this'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0
				  || contained_in (block_found,
						   innermost_block))
				innermost_block = block_found;
			      /* EMBARCADERO Local: begin self member access. */
			      /* We need type of this.  */
			      this_val = value_of_this (0);
			      if (this_val)
				current_type = value_type (this_val);
			      else
				current_type = NULL;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename#2");
			      /* Try to lookup the field. */
			      if (!current_type ||
				  (lookup_struct_elt_type (
				     current_type,
				     copy_name ($1.stoken), 1) == NULL))
			        {
				  /* Field lookup failed. See if it's a property
				     or method.  */
				  sym = lookup_symbol ("self", expression_context_block,
						       VAR_DOMAIN, 0);
				  if (sym && sym->type)
				    { current_type = sym->type;
				      DUMP_CURRENT_TYPE ("variable:name_not_typename#3");
				    }
				  if (!current_type)
				    {
				      /* We shouldn't have gotten here if we
					 couldn't find the "this" type. */
				      error (_("\"self\" symbol not found."));
				      goto done_variable;
				    }
				  while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				    { /* Dereference the object. */ 
				      current_type = TYPE_TARGET_TYPE (current_type);
				      DUMP_CURRENT_TYPE ("variable:name_not_typename#4");
				    }
				  /* Special case: evaluate "method"
				     as a function call. */
			          current_method = lookup_struct_elt_fn_field (
				    current_type, $1.stoken.ptr, 0);
			          if (!current_method)
			            current_property = lookup_struct_elt_prop_field (
				      current_type, $1.stoken.ptr);
			          if (!current_method && !current_property)
				    {
				      /* We shouldn't have gotten here if it's
					 not a method or property. */
				      error (_("\"%s\" not a method or property."),
					     $1.stoken.ptr);
				      goto done_variable;
				    }
				  /* If property read is just a field, use that field.
				     FIXME: need to support writing! */
				  if (current_property &&
				      PROP_FIELD_READ_NAME(*current_property) &&
				      !PROP_FIELD_GETTER(*current_property))
				    { char* prop_read_name =
					PROP_FIELD_READ_NAME(*current_property);
				      $1.stoken.ptr = prop_read_name;
				      $1.stoken.length = strlen(prop_read_name);

				      write_exp_elt_opcode (OP_THIS);
				      write_exp_elt_opcode (OP_THIS);
				      write_exp_elt_opcode (STRUCTOP_PTR);
				      write_exp_string ($1.stoken);
				      write_exp_elt_opcode (STRUCTOP_PTR);
				      /* Reset the type to the type of the field. */
				      current_type = current_property->type;
				      DUMP_CURRENT_TYPE ("variable:name_not_typename#5");
				      current_property = 0;
				    }
				  /* If property read is a getter, use that method.
				     FIXME: need to support writing! */
				  else if (current_property &&
					   PROP_FIELD_READ_NAME(*current_property) &&
					   PROP_FIELD_GETTER(*current_property))
				    { char* prop_read_name =
					PROP_FIELD_READ_NAME(*current_property);
				      $1.stoken.ptr = prop_read_name;
				      $1.stoken.length = strlen(prop_read_name);
				      current_method = lookup_struct_elt_fn_field (
					current_type, prop_read_name, 0);
				      current_property = 0;
				      goto do_this_method;
				    }
				  else if (current_property)
				    { error (_("Property \"%s\" not readable."),
					     $1.stoken.ptr);
				      current_property = 0;
				      goto done_variable;
				    }
				  else if (current_method)
				    {
				    do_this_method:
				      /* Write out the this symbol. */
				      if (!sym)
					{
					  error (_("\"self\" symbol not found."));
					  goto done_variable;
					}
			              write_exp_elt_opcode (OP_VAR_VALUE);
			              write_exp_elt_block (NULL);
			              write_exp_elt_sym (sym);
			              write_exp_elt_opcode (OP_VAR_VALUE);

				      /* Then call the method. */
				      write_exp_elt_opcode (STRUCTOP_STRUCT);
				      write_exp_string ($1.stoken);
				      write_exp_elt_opcode (STRUCTOP_STRUCT);
				      start_arglist ();
				      write_exp_elt_opcode (OP_FUNCALL);
				      write_exp_elt_longcst ((LONGEST) end_arglist ());
				      write_exp_elt_opcode (OP_FUNCALL); 
				      /* Reset the type to the return type of the method. */
				      if (current_method)
					current_type = TYPE_TARGET_TYPE (current_method->type);
				      DUMP_CURRENT_TYPE ("variable:name_not_typename#6");
				      current_method = 0;
				    }
				  else
				    {
				      goto do_this_field;
				    }
				}
			      /* EMBARCADERO Local: end self member access. */
			      else
				{
				do_this_field:
				  /* It's a normal field. */
				  write_exp_elt_opcode (OP_THIS);
				  write_exp_elt_opcode (OP_THIS);
				  write_exp_elt_opcode (STRUCTOP_PTR);
				  write_exp_string ($1.stoken);
				  write_exp_elt_opcode (STRUCTOP_PTR);
				  /* Reset the type to the type of the field. */
				  if (current_type)
				    { current_type = lookup_struct_elt_type (
					current_type,
					copy_name ($1.stoken), 0);
				      DUMP_CURRENT_TYPE ("variable:name_not_typename#7");
				    }
				}
			    }
			  /* EMBARCADERO LOCAL: begin nested functions */
			  /* Is it a field of '__FRAME__' to be passed
			     to a nested function?  */
			  else if ($1.is_a_field_of_this == ifk_frame)
				   /* is_a_field_of_this == ifk_frame means the
				      field is a member of an implicit frame structure
				      to be passed to a nested function.  */
			    {
			      /* Lookup "__FRAME__". */
			      /* Object pascal: it hangs off of `__FRAME__'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0
				  || contained_in (block_found,
						   innermost_block))
				innermost_block = block_found;
			      sym = lookup_symbol ("__FRAME__",
						   expression_context_block,
						   VAR_DOMAIN, 0);

			      /* Get the frameptr symbol. */
			      if (!sym || !sym->type)
				{
				  /* We shouldn't have gotten here if we
				      couldn't find the "this" type. */
				  error (_("\"__FRAME__\" symbol not found."));
				  goto done_variable_call;
				}
			      current_type = sym->type;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename#12");
			      /* Lookup the field. */
			      while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				{ /* Dereference the object. */ 
				  current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("variable:name_not_typename#13");
				}
			      /* Write out the frameptr symbol. */
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      /* Followed by the field. */
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      write_exp_string ($1.stoken);
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      /* Reset the type to the type of the field. */
			      if (current_type)
				{ current_type = lookup_struct_elt_type (
				    current_type,
				    copy_name ($1.stoken), 0);
				  DUMP_CURRENT_TYPE ("variable:name_not_typename#17");
				}
			    }
			  /* Is it a field of '__FRAMEPTR__' passed in
			     from an outer function?  */
			  else if ($1.is_a_field_of_this)
			    {
			      /* is_a_field_of_this == ifk_frameptr means the
				 field is a member of an implicit frame structure
				 whose pointer was passed in from an outer function.  */
			      gdb_assert ($1.is_a_field_of_this == ifk_frameptr);
			      /* Lookup "__FRAMEPTR__". */
			      /* Object pascal: it hangs off of `__FRAMEPTR__'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0
				  || contained_in (block_found,
						   innermost_block))
				innermost_block = block_found;
			      sym = lookup_symbol ("__FRAMEPTR__",
						   expression_context_block,
						   VAR_DOMAIN, 0);

			      /* Get the frameptr symbol. */
			      if (!sym || !sym->type)
				{
				  /* We shouldn't have gotten here if we
				      couldn't find the "this" type. */
				  error (_("\"__FRAMEPTR__\" symbol not found."));
				  goto done_variable_call;
				}
			      current_type = sym->type;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename#22");
			      /* Lookup the field. */
			      while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				{ /* Dereference the object. */ 
				  current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("variable:name_not_typename#23");
				}
			      /* Write out the frameptr symbol. */
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      /* Followed by the field. */
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      write_exp_string ($1.stoken);
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      /* Reset the type to the type of the field. */
			      if (current_type)
				{ current_type = lookup_struct_elt_type (
				    current_type,
				    copy_name ($1.stoken), 0);
				  DUMP_CURRENT_TYPE ("variable:name_not_typename#27");
				}
			    }
			  /* EMBARCADERO LOCAL: end nested functions */
			  else
			    {
			      struct minimal_symbol *msymbol;
			      char *arg = copy_name ($1.stoken);

			      msymbol =
				lookup_minimal_symbol (arg, NULL, NULL);
			      if (msymbol != NULL)
				write_exp_msymbol (msymbol);
			      else if (!have_full_symbols ()
				       && !have_partial_symbols ())
				error (_("No symbol table is loaded.  "
				       "Use the \"file\" command."));
			      else
				error (_("No symbol \"%s\" in current context."),
				       copy_name ($1.stoken));
			    }
			  done_variable: ;
			}
	;

/* EMBARCADERO Local: begin self member access. */
variable:	name_not_typename '('
			/* This is to save the value of arglist_len
			   being accumulated by an outer function call.  */
			{ struct symbol *sym = $1.sym;
			  /* EMBARCADERO FIXME: should start_arglist() come
			     after we determine the method to call?  */
			  start_arglist (); 
			  if (sym)
			    {
			      if (symbol_read_needs_frame (sym))
				{
				  if (innermost_block == 0
				      || contained_in (block_found,
						       innermost_block))
				    innermost_block = block_found;
				}
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      /* We want to use the selected frame, not
				 another more inner frame which happens to
				 be in the same block.  */
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      current_type = sym->type;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename'(arglist')''");
			    }
			  else if ($1.is_a_field_of_this)
			    {
			      /* Lookup "self". */
			      /* Object pascal: it hangs off of `this'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0
				  || contained_in (block_found,
				    		   innermost_block))
				innermost_block = block_found;
			      sym = lookup_symbol ("self", expression_context_block,
						   VAR_DOMAIN, 0);
			      /* Get the this symbol. */
			      if (!sym || !sym->type)
				{
				  /* We shouldn't have gotten here if we
				      couldn't find the "this" type. */
				  error (_("\"self\" symbol not found."));
				  goto done_variable_call;
				}
			      current_type = sym->type;
			      DUMP_CURRENT_TYPE ("variable:name_not_typename'(arglist')''#2");
			      /* Lookup the field. */
			      while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
				{ /* Dereference the object. */ 
				  current_type = TYPE_TARGET_TYPE (current_type);
				  DUMP_CURRENT_TYPE ("variable:name_not_typename'('arglist')'#3");
				}
			      /* Write out the this symbol. */
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      write_exp_elt_block (NULL);
			      write_exp_elt_sym (sym);
			      write_exp_elt_opcode (OP_VAR_VALUE);
			      /* And prepare to call the method. */
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($1.stoken);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      /* Reset the type to the type of the method. */
			      current_method = lookup_struct_elt_fn_field (
				current_type, $1.stoken.ptr, 0);
			      if (current_method)
			      { current_type = current_method->type;
				DUMP_CURRENT_TYPE ("variable:name_not_typename'('arglist')'#4");
			      }
			      current_method = 0;
			    }
			  else
			    {
			      struct minimal_symbol *msymbol;
			      char *arg = copy_name ($1.stoken);

			      msymbol =
				lookup_minimal_symbol (arg, NULL, NULL);
			      if (msymbol != NULL)
				write_exp_msymbol (msymbol);
			      else if (!have_full_symbols ()
				       && !have_partial_symbols ())
				error (_("No symbol table is loaded.  "
				       "Use the \"file\" command."));
			      else
				error (_("No symbol \"%s\" in current context."),
				       copy_name ($1.stoken));
			    }
			done_variable_call: ;
			  push_current_type ();
			}
		arglist ')'	%prec ARROW
			{
			  write_exp_elt_opcode (OP_FUNCALL);
			  write_exp_elt_longcst ((LONGEST) end_arglist ());
			  write_exp_elt_opcode (OP_FUNCALL); 
			  pop_current_type (); 
			  /* Reset the type to the return type of the method. */
			  if (current_type)
			  { current_type = TYPE_TARGET_TYPE (current_type);
			    DUMP_CURRENT_TYPE ("variable:name_not_typename'('arglist')'#5");
			  }
			}
	;
/* EMBARCADERO Local: end self member access. */


ptype	:	typebase
	;

/* We used to try to recognize more pointer to member types here, but
   that didn't work (shift/reduce conflicts meant that these rules never
   got executed).  The problem is that
     int (foo::bar::baz::bizzle)
   is a function type but
     int (foo::bar::baz::bizzle::*)
   is a pointer to member type.  Stroustrup loses again!  */

type	:	ptype
	;

typebase  /* Implements (approximately): (type-qualifier)* type-specifier */
	:	'^' typebase
			{ $$ = lookup_pointer_type ($2);
			  /* EMBARCADERO LOCAL Delphi units lookup */
			  current_type = $$;
			  DUMP_CURRENT_TYPE ("typebase:'^'typebase"); }
	|	TYPENAME
			{ $$ = $1.type;
			  /* EMBARCADERO LOCAL Delphi units lookup */
			  current_type = $$;
			  DUMP_CURRENT_TYPE ("typebase:TYPENAME");
			  DUMP_TYPE ("typebase:TYPENAME#2", $1.type); }
	|	STRUCT name
			{ $$ = lookup_struct (copy_name ($2),
					      expression_context_block); }
	|	CLASS name
			{ $$ = lookup_struct (copy_name ($2),
					      expression_context_block); }
	/* "const" and "volatile" are curently ignored.  A type qualifier
	   after the type is handled in the ptype rule.  I think these could
	   be too.  */
	;

ident	:	NAME { $$ = $1.stoken;
		       DUMP_CURRENT_TYPE ("ident:NAME"); }
	|	IDENT
	|	TYPENAME { $$ = $1.stoken;
			   /* EMBARCADERO LOCAL Delphi units lookup */
			   current_type = $1.type;
			   DUMP_CURRENT_TYPE ("ident:TYPENAME"); }
	/* EMBARCADERO LOCAL Delphi methods */
        |       BLOCKNAME
	;

name	:	NAME { $$ = $1.stoken;
		       DUMP_CURRENT_TYPE ("name:NAME"); }
	|	BLOCKNAME { $$ = $1.stoken; }
	|	TYPENAME { $$ = $1.stoken;
			   /* EMBARCADERO LOCAL Delphi units lookup */
			   current_type = $1.type;
			   DUMP_CURRENT_TYPE ("name:TYPENAME"); }
	|	NAME_OR_INT  { $$ = $1.stoken; }
	|	IDENT { /* EMBARCADERO LOCAL begin Delphi units lookup */
			DUMP_CURRENT_TYPE ("name:IDENT");
			if (saw_structop && current_type)
			  { while (TYPE_CODE (current_type) == TYPE_CODE_PTR)
			      { /* Dereference the object. */ 
				current_type = TYPE_TARGET_TYPE (current_type);
				DUMP_CURRENT_TYPE ("name:IDENT#1");
			      }
			    if (TYPE_CODE (current_type) == TYPE_CODE_NAMESPACE)
			    { const char *parent_name
				= TYPE_TAG_NAME (current_type);
			      struct symbol *sym
				= cp_lookup_symbol_namespace (parent_name,
							      $1.ptr,
							      expression_context_block,
							      VAR_DOMAIN);
			      current_type = sym ? sym->type : NULL;
			    }
#ifdef DAWN_NESTED_FUNCS
			      { const char *parent_name
				  = TYPE_TAG_NAME (current_type);
				struct symbol *sym
				  = cp_lookup_symbol_namespace (parent_name,
								$1.ptr,
								NULL,
								expression_context_block,
								VAR_DOMAIN,
								0,
								NULL);
				current_type = sym ? sym->type : NULL;
			      }
#endif
			    else
			      current_type = lookup_struct_elt_type (
				current_type, $1.ptr, 0);
			    DUMP_CURRENT_TYPE ("name:IDENT#1");
			  }
			/* EMBARCADERO LOCAL end Delphi units lookup */
		      }
	;

name_not_typename :	NAME
	|	BLOCKNAME
	|	IDENT
/* These would be useful if name_not_typename was useful, but it is just
   a fake for "variable", so these cause reduce/reduce conflicts because
   the parser can't tell whether NAME_OR_INT is a name_not_typename (=variable,
   =exp) or just an exp.  If name_not_typename was ever used in an lvalue
   context where only a name could occur, this might be useful.
  	|	NAME_OR_INT
 */
	;

%%

/* Take care of parsing a number (anything that starts with a digit).
   Set yylval and return the token type; update lexptr.
   LEN is the number of characters in it.  */

/*** Needs some error checking for the float case ***/

static int
parse_number (char *p, int len, int parsed_float, YYSTYPE *putithere)
{
  /* FIXME: Shouldn't these be unsigned?  We don't deal with negative values
     here, and we do kind of silly things like cast to unsigned.  */
  LONGEST n = 0;
  LONGEST prevn = 0;
  ULONGEST un;

  int i = 0;
  int c;
  int base = input_radix;
  int unsigned_p = 0;

  /* Number of "L" suffixes encountered.  */
  int long_p = 0;

  /* We have found a "L" or "U" suffix.  */
  int found_suffix = 0;

  ULONGEST high_bit;
  struct type *signed_type;
  struct type *unsigned_type;

  if (parsed_float)
    {
      if (! parse_c_float (parse_gdbarch, p, len,
			   &putithere->typed_val_float.dval,
			   &putithere->typed_val_float.type))
	return ERROR;
      return FLOAT;
    }

  /* Handle base-switching prefixes 0x, 0t, 0d, 0.  */
  if (p[0] == '0')
    switch (p[1])
      {
      case 'x':
      case 'X':
	if (len >= 3)
	  {
	    p += 2;
	    base = 16;
	    len -= 2;
	  }
	break;

      case 't':
      case 'T':
      case 'd':
      case 'D':
	if (len >= 3)
	  {
	    p += 2;
	    base = 10;
	    len -= 2;
	  }
	break;

      default:
	base = 8;
	break;
      }

  while (len-- > 0)
    {
      c = *p++;
      if (c >= 'A' && c <= 'Z')
	c += 'a' - 'A';
      if (c != 'l' && c != 'u')
	n *= base;
      if (c >= '0' && c <= '9')
	{
	  if (found_suffix)
	    return ERROR;
	  n += i = c - '0';
	}
      else
	{
	  if (base > 10 && c >= 'a' && c <= 'f')
	    {
	      if (found_suffix)
		return ERROR;
	      n += i = c - 'a' + 10;
	    }
	  else if (c == 'l')
	    {
	      ++long_p;
	      found_suffix = 1;
	    }
	  else if (c == 'u')
	    {
	      unsigned_p = 1;
	      found_suffix = 1;
	    }
	  else
	    return ERROR;	/* Char not a digit */
	}
      if (i >= base)
	return ERROR;		/* Invalid digit in this base.  */

      /* Portably test for overflow (only works for nonzero values, so make
	 a second check for zero).  FIXME: Can't we just make n and prevn
	 unsigned and avoid this?  */
      if (c != 'l' && c != 'u' && (prevn >= n) && n != 0)
	unsigned_p = 1;		/* Try something unsigned.  */

      /* Portably test for unsigned overflow.
	 FIXME: This check is wrong; for example it doesn't find overflow
	 on 0x123456789 when LONGEST is 32 bits.  */
      if (c != 'l' && c != 'u' && n != 0)
	{
	  if ((unsigned_p && (ULONGEST) prevn >= (ULONGEST) n))
	    error (_("Numeric constant too large."));
	}
      prevn = n;
    }

  /* An integer constant is an int, a long, or a long long.  An L
     suffix forces it to be long; an LL suffix forces it to be long
     long.  If not forced to a larger size, it gets the first type of
     the above that it fits in.  To figure out whether it fits, we
     shift it right and see whether anything remains.  Note that we
     can't shift sizeof (LONGEST) * HOST_CHAR_BIT bits or more in one
     operation, because many compilers will warn about such a shift
     (which always produces a zero result).  Sometimes gdbarch_int_bit
     or gdbarch_long_bit will be that big, sometimes not.  To deal with
     the case where it is we just always shift the value more than
     once, with fewer bits each time.  */

  un = (ULONGEST)n >> 2;
  if (long_p == 0
      && (un >> (gdbarch_int_bit (parse_gdbarch) - 2)) == 0)
    {
      high_bit = ((ULONGEST)1) << (gdbarch_int_bit (parse_gdbarch) - 1);

      /* A large decimal (not hex or octal) constant (between INT_MAX
	 and UINT_MAX) is a long or unsigned long, according to ANSI,
	 never an unsigned int, but this code treats it as unsigned
	 int.  This probably should be fixed.  GCC gives a warning on
	 such constants.  */

      unsigned_type = parse_type->builtin_unsigned_int;
      signed_type = parse_type->builtin_int;
    }
  else if (long_p <= 1
	   && (un >> (gdbarch_long_bit (parse_gdbarch) - 2)) == 0)
    {
      high_bit = ((ULONGEST)1) << (gdbarch_long_bit (parse_gdbarch) - 1);
      unsigned_type = parse_type->builtin_unsigned_long;
      signed_type = parse_type->builtin_long;
    }
  else
    {
      int shift;
      if (sizeof (ULONGEST) * HOST_CHAR_BIT
	  < gdbarch_long_long_bit (parse_gdbarch))
	/* A long long does not fit in a LONGEST.  */
	shift = (sizeof (ULONGEST) * HOST_CHAR_BIT - 1);
      else
	shift = (gdbarch_long_long_bit (parse_gdbarch) - 1);
      high_bit = (ULONGEST) 1 << shift;
      unsigned_type = parse_type->builtin_unsigned_long_long;
      signed_type = parse_type->builtin_long_long;
    }

   putithere->typed_val_int.val = n;

   /* If the high bit of the worked out type is set then this number
      has to be unsigned.  */

   if (unsigned_p || (n & high_bit))
     {
       putithere->typed_val_int.type = unsigned_type;
     }
   else
     {
       putithere->typed_val_int.type = signed_type;
     }

   return INT;
}


struct type_push
{
  struct type *stored;
  struct type_push *next;
};

static struct type_push *tp_top = NULL;

static void
push_current_type (void)
{
  struct type_push *tpnew;
  tpnew = (struct type_push *) malloc (sizeof (struct type_push));
  tpnew->next = tp_top;
  tpnew->stored = current_type;
  current_type = NULL;
  DUMP_CURRENT_TYPE ("push_current_type");
  tp_top = tpnew;
}

static void
pop_current_type (void)
{
  struct type_push *tp = tp_top;
  if (tp)
    {
      current_type = tp->stored;
      tp_top = tp->next;
      free (tp);
    }
  DUMP_CURRENT_TYPE ("pop_current_type");
}

/* EMBARCADERO Local begin parser debugging */
void
dump_current_type (const char *str)
{
  const char *name = (current_type && TYPE_NAME (current_type))
		     ? TYPE_NAME (current_type)
		     : "(nil)";
  printf ("   DBG:: %s current_type=%p(\"%s\")\n", str, current_type, name);
#ifdef YYDEBUG_VERBOSE
  printf ("   DBG:: in_parse_field=%d\n", in_parse_field);
  printf ("   DBG:: saw_structop=%d,last_was_structop=%d\n", saw_structop, last_was_structop);
#endif
}

void
dump_type (const char *str, struct type *type)
{
  const char *name = (type && TYPE_NAME (type))
		     ? TYPE_NAME (type)
		     : "(nil)";
  printf ("   DBG:: %s type=%p(\"%s\")\n", str, type, name);
}

void
dump_string (const char *str, const char *str2)
{
  const char *name = str2 ? str2 : "(nil)";
  printf ("   DBG:: %s \"%s\"\n", str, name);
}

void
dump_stoken (const char *str, struct stoken *stok)
{
  const char *name = stok->ptr ? stok->ptr : "(nil)";
  printf ("   DBG:: %s stok=\"%s\"\n", str, name);
}

void
dump_ttype (const char *str, struct ttype *tsym)
{
  const char *name = (tsym->type && TYPE_NAME (tsym->type))
		     ? TYPE_NAME (tsym->type)
		     : tsym->stoken.ptr ? tsym->stoken.ptr : "(nil)";
  printf ("   DBG:: %s tsym=%p,\"%s\"\n", str, tsym->type, name);
}

void
dump_symtoken (const char *str, struct symtoken *ssym)
{
  const char *name = (ssym->sym && SYMBOL_PRINT_NAME (ssym->sym))
		     ? SYMBOL_PRINT_NAME (ssym->sym)
		     : ssym->stoken.ptr ? ssym->stoken.ptr : "(nil)";
  printf ("   DBG:: %s ssym=%p,\"%s\",is_a_field_of_this=%d\n",
	  str, ssym->sym, name, ssym->is_a_field_of_this);
}
/* EMBARCADERO Local end parser debugging */

struct token
{
  char *operator;
  int token;
  enum exp_opcode opcode;
};

static const struct token tokentab3[] =
  {
    {"shr", RSH, BINOP_END},
    {"shl", LSH, BINOP_END},
    {"and", ANDAND, BINOP_END},
    {"div", DIV, BINOP_END},
    {"not", NOT, BINOP_END},
    {"mod", MOD, BINOP_END},
    {"inc", INCREMENT, BINOP_END},
    {"dec", DECREMENT, BINOP_END},
    {"xor", XOR, BINOP_END}
  };

static const struct token tokentab2[] =
  {
    {"or", OR, BINOP_END},
    {"<>", NOTEQUAL, BINOP_END},
    {"<=", LEQ, BINOP_END},
    {">=", GEQ, BINOP_END},
    {":=", ASSIGN, BINOP_END},
    {"::", COLONCOLON, BINOP_END} };

/* Allocate uppercased var: */
/* make an uppercased copy of tokstart.  */
static char * uptok (tokstart, namelen)
  char *tokstart;
  int namelen;
{
  int i;
  char *uptokstart = (char *)malloc(namelen+1);
  for (i = 0;i <= namelen;i++)
    {
      if ((tokstart[i]>='a' && tokstart[i]<='z'))
        uptokstart[i] = tokstart[i]-('a'-'A');
      else
        uptokstart[i] = tokstart[i];
    }
  uptokstart[namelen]='\0';
  return uptokstart;
}

/* Read one token, getting characters through lexptr.  */

static int
yylex (void)
{
  int c;
  int namelen;
  unsigned int i;
  char *tokstart;
  char *uptokstart;
  char *tokptr;
  int explen, tempbufindex;
  static char *tempbuf;
  static int tempbufsize;

  /* EMBARCADERO LOCAL Delphi units lookup */
  saw_structop = last_was_structop;
  last_was_structop = 0;

 retry:

  prev_lexptr = lexptr;

  tokstart = lexptr;
  explen = strlen (lexptr);
  /* See if it is a special token of length 3.  */
  if (explen > 2)
    for (i = 0; i < sizeof (tokentab3) / sizeof (tokentab3[0]); i++)
      if (strncasecmp (tokstart, tokentab3[i].operator, 3) == 0
          && (!isalpha (tokentab3[i].operator[0]) || explen == 3
              || (!isalpha (tokstart[3])
		  && !isdigit (tokstart[3]) && tokstart[3] != '_')))
        {
          lexptr += 3;
          yylval.opcode = tokentab3[i].opcode;
          return tokentab3[i].token;
        }

  /* See if it is a special token of length 2.  */
  if (explen > 1)
  for (i = 0; i < sizeof (tokentab2) / sizeof (tokentab2[0]); i++)
      if (strncasecmp (tokstart, tokentab2[i].operator, 2) == 0
          && (!isalpha (tokentab2[i].operator[0]) || explen == 2
              || (!isalpha (tokstart[2])
		  && !isdigit (tokstart[2]) && tokstart[2] != '_')))
        {
          lexptr += 2;
          yylval.opcode = tokentab2[i].opcode;
          return tokentab2[i].token;
        }

  switch (c = *tokstart)
    {
    case 0:
      if (saw_structop && search_field)
	return COMPLETE;
      else
       return 0;

    case ' ':
    case '\t':
    case '\n':
      lexptr++;
      goto retry;

    case '\'':
      /* We either have a character constant ('0' or '\177' for example)
	 or we have a quoted symbol reference ('foo(int,int)' in object pascal
	 for example).  */
      /* EMBARCADERO LOCAL string literals */
      /* '' and 'abc' are strings in Delphi, while 'c' can be either a
	 character or a string, depending on the context.  Overloading
	 prefers char however, so we will too.  */
      lexptr++;
      c = *lexptr++;
      if (c == '\\')
	c = parse_escape (parse_gdbarch, &lexptr);
      else if (c == '\'')
	/* EMBARCADERO LOCAL begin string literals */
	{
	  /* '' is an empty string.  */
	  static char *tempbuf = (char*)"";
	  yylval.sval.ptr = tempbuf;
	  yylval.sval.length = 0;
	  DUMP_CURRENT_TYPE ("returning STRING");
	  return (STRING);
	}
	/* EMBARCADERO LOCAL end string literals */

      yylval.typed_val_int.val = c;
      /* EMBARCADERO LOCAL string literals */
      /* was: yylval.typed_val_int.type = parse_type->builtin_char; */
      yylval.typed_val_int.type = pascal_char_type (parse_gdbarch);

      c = *lexptr++;
      if (c != '\'')
	{
	  namelen = skip_quoted (tokstart) - tokstart;
	  if (namelen > 2)
	    {
#if 0 /* EMBARCADERO LOCAL string literals */
	      lexptr = tokstart + namelen;
	      if (lexptr[-1] != '\'')
		error (_("Unmatched single quote."));
	      namelen -= 2;
              tokstart++;
              uptokstart = uptok(tokstart,namelen);
	      goto tryname;
#else
	      /* EMBARCADERO LOCAL begin string literals */
	      /* Build the gdb internal form of the input string in tempbuf,
		 translating any standard C escape forms seen.  Note that the
		 buffer is null byte terminated *only* for the convenience of
		 debugging gdb itself and printing the buffer contents when
		 the buffer contains no embedded nulls.  Gdb does not depend
		 upon the buffer being null byte terminated, it uses the length
		 string instead.  This allows gdb to handle C strings (as well
		 as strings in other languages) with embedded null bytes.  */

	      int done = 0;
	      tokptr = ++tokstart;
	      tempbufindex = 0;

	      do {
		/* Grow the static temp buffer if necessary, including
		   allocating the first one on demand.  */
		if (tempbufindex + charsize >= tempbufsize)
		  {
		    tempbuf = (char *) realloc (tempbuf, tempbufsize += 64);
		  }

		/* FIXME: need to handle multibyte characters.  */
		switch (*tokptr)
		  {
		  case '\0':
		  case '\'':
		    if (tokptr[1] == '\'')
		      {
			/* '' in a single quoted string is a single '.  */
			*((chartype*)(tempbuf + tempbufindex)) = '\'';
			tempbufindex += charsize;
			tokptr += 2;
			continue;
		      }
		    /* Done!  */
		    done = 1;
		    break;
		  case '\\':
		    tokptr++;
		    c = parse_escape (parse_gdbarch, &tokptr);
		    if (c == -1)
		      {
			continue;
		      }
		    *((chartype*)(tempbuf + tempbufindex)) = c;
		    tempbufindex += charsize;
		    break;
		  default:
		    *((chartype*)(tempbuf + tempbufindex)) = *tokptr++;
		    tempbufindex += charsize;
		    break;
		  }
	      } while (!done && (*tokptr != '\0'));
	      if (*tokptr++ != '\'')
		{
		  error (_("Unterminated string in expression."));
		}
	      /* NULL terminator for debugging purposes only.  */
	      *((chartype*)(tempbuf + tempbufindex)) = '\0'; /* See note above.  */
	      yylval.sval.ptr = tempbuf;
	      yylval.sval.length = tempbufindex;
	      lexptr = tokptr;
	      DUMP_CURRENT_TYPE ("returning STRING#2");
	      return (STRING);
	      /* EMBARCADERO LOCAL end string literals */
#endif
	    }
	  error (_("Invalid character constant."));
	}
      return INT;

    case '(':
      paren_depth++;
      lexptr++;
      return c;

    case ')':
      if (paren_depth == 0)
	return 0;
      paren_depth--;
      lexptr++;
      return c;

    case ',':
      if (comma_terminates && paren_depth == 0)
	return 0;
      lexptr++;
      return c;

    case '.':
      /* Might be a floating point number.  */
      if (lexptr[1] < '0' || lexptr[1] > '9')
	{
	  /* EMBARCADERO LOCAL Delphi units */
	  /* Treat Dalphi units (namespaces) as structs for the purposes
	     of lookup (was: if (in_parse_field)).  */
	  last_was_structop = 1;
	  DUMP_CURRENT_TYPE ("case'.'");
	  goto symbol;		/* Nope, must be a symbol. */
	}

      /* FALL THRU into number case.  */

    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      {
	/* It's a number.  */
	int got_dot = 0, got_e = 0, toktype;
	char *p = tokstart;
	int hex = input_radix > 10;

	if (c == '0' && (p[1] == 'x' || p[1] == 'X'))
	  {
	    p += 2;
	    hex = 1;
	  }
	else if (c == '0' && (p[1]=='t' || p[1]=='T'
			      || p[1]=='d' || p[1]=='D'))
	  {
	    p += 2;
	    hex = 0;
	  }

	for (;; ++p)
	  {
	    /* This test includes !hex because 'e' is a valid hex digit
	       and thus does not indicate a floating point number when
	       the radix is hex.  */
	    if (!hex && !got_e && (*p == 'e' || *p == 'E'))
	      got_dot = got_e = 1;
	    /* This test does not include !hex, because a '.' always indicates
	       a decimal floating point number regardless of the radix.  */
	    else if (!got_dot && *p == '.')
	      got_dot = 1;
	    else if (got_e && (p[-1] == 'e' || p[-1] == 'E')
		     && (*p == '-' || *p == '+'))
	      /* This is the sign of the exponent, not the end of the
		 number.  */
	      continue;
	    /* We will take any letters or digits.  parse_number will
	       complain if past the radix, or if L or U are not final.  */
	    else if ((*p < '0' || *p > '9')
		     && ((*p < 'a' || *p > 'z')
				  && (*p < 'A' || *p > 'Z')))
	      break;
	  }
	toktype = parse_number (tokstart,
				p - tokstart, got_dot | got_e, &yylval);
        if (toktype == ERROR)
	  {
	    char *err_copy = (char *) alloca (p - tokstart + 1);

	    memcpy (err_copy, tokstart, p - tokstart);
	    err_copy[p - tokstart] = 0;
	    error (_("Invalid number \"%s\"."), err_copy);
	  }
	lexptr = p;
	return toktype;
      }

    case '+':
    case '-':
    case '*':
    case '/':
    case '|':
    case '&':
    case '^':
    case '~':
    case '!':
    case '@':
    case '<':
    case '>':
    case '[':
    case ']':
    case '?':
    case ':':
    case '=':
    case '{':
    case '}':
    symbol:
      lexptr++;
      return c;

    case '"':

      /* Build the gdb internal form of the input string in tempbuf,
	 translating any standard C escape forms seen.  Note that the
	 buffer is null byte terminated *only* for the convenience of
	 debugging gdb itself and printing the buffer contents when
	 the buffer contains no embedded nulls.  Gdb does not depend
	 upon the buffer being null byte terminated, it uses the length
	 string instead.  This allows gdb to handle C strings (as well
	 as strings in other languages) with embedded null bytes.  */

      tokptr = ++tokstart;
      tempbufindex = 0;

      do {
	/* Grow the static temp buffer if necessary, including allocating
	   the first one on demand.  */
	if (tempbufindex + 1 >= tempbufsize)
	  {
	    tempbuf = (char *) realloc (tempbuf, tempbufsize += 64);
	  }

	switch (*tokptr)
	  {
	  case '\0':
	  case '"':
	    /* Do nothing, loop will terminate.  */
	    break;
	  case '\\':
	    tokptr++;
	    c = parse_escape (parse_gdbarch, &tokptr);
	    if (c == -1)
	      {
		continue;
	      }
	    tempbuf[tempbufindex++] = c;
	    break;
	  default:
	    tempbuf[tempbufindex++] = *tokptr++;
	    break;
	  }
      } while ((*tokptr != '"') && (*tokptr != '\0'));
      if (*tokptr++ != '"')
	{
	  error (_("Unterminated string in expression."));
	}
      tempbuf[tempbufindex] = '\0';	/* See note above.  */
      yylval.sval.ptr = tempbuf;
      yylval.sval.length = tempbufindex;
      lexptr = tokptr;
      DUMP_CURRENT_TYPE ("returning STRING#3");
      return (STRING);
    }

  if (!(c == '_' || c == '$'
	|| (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')))
    /* We must have come across a bad character (e.g. ';').  */
    error (_("Invalid character '%c' in expression."), c);

  /* It's a name.  See how long it is.  */
  namelen = 0;
  for (c = tokstart[namelen];
       (c == '_' || c == '$' || (c >= '0' && c <= '9')
	|| (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '<');)
    {
      /* Template parameter lists are part of the name.
	 FIXME: This mishandles `print $a<4&&$a>3'.  */
      if (c == '<')
	{
	  int i = namelen;
	  int nesting_level = 1;
	  while (tokstart[++i])
	    {
	      if (tokstart[i] == '<')
		nesting_level++;
	      else if (tokstart[i] == '>')
		{
		  if (--nesting_level == 0)
		    break;
		}
	    }
	  if (tokstart[i] == '>')
	    namelen = i;
	  else
	    break;
	}

      /* do NOT uppercase internals because of registers !!!  */
      c = tokstart[++namelen];
    }

  uptokstart = uptok(tokstart,namelen);

  /* The token "if" terminates the expression and is NOT
     removed from the input stream.  */
  if (namelen == 2 && uptokstart[0] == 'I' && uptokstart[1] == 'F')
    {
      free (uptokstart);
      return 0;
    }

  lexptr += namelen;

#if 0 /* EMBARCADERO LOCAL string literals */
  tryname:
#endif

  /* Catch specific keywords.  Should be done with a data structure.  */
  switch (namelen)
    {
    case 6:
      if (strcmp (uptokstart, "OBJECT") == 0)
	{
	  free (uptokstart);
	  return CLASS;
	}
      if (strcmp (uptokstart, "RECORD") == 0)
	{
	  free (uptokstart);
	  return STRUCT;
	}
      if (strcmp (uptokstart, "SIZEOF") == 0)
	{
	  free (uptokstart);
	  return SIZEOF;
	}
      break;
    case 5:
      if (strcmp (uptokstart, "CLASS") == 0)
	{
	  free (uptokstart);
	  return CLASS;
	}
      if (strcmp (uptokstart, "FALSE") == 0)
	{
          yylval.lval = 0;
	  free (uptokstart);
          return FALSEKEYWORD;
        }
      break;
    case 4:
      if (strcmp (uptokstart, "TRUE") == 0)
	{
          yylval.lval = 1;
	  free (uptokstart);
  	  return TRUEKEYWORD;
        }
      if (strcmp (uptokstart, "SELF") == 0)
        {
          /* Here we search for 'this' like
             inserted in FPC stabs debug info.  */
	  // EMBARCADERO FIXME: should be "self"
	  static const char this_name[] = "this";

	  if (lookup_symbol (this_name, expression_context_block,
			     VAR_DOMAIN, (int *) NULL))
	    {
	      free (uptokstart);
	      DUMP_CURRENT_TYPE ("returning THIS");
	      return THIS;
	    }
	}
      break;
    default:
      break;
    }

  yylval.sval.ptr = tokstart;
  yylval.sval.length = namelen;

  if (*tokstart == '$')
    {
      char c;
      /* $ is the normal prefix for pascal hexadecimal values
        but this conflicts with the GDB use for debugger variables
        so in expression to enter hexadecimal values
        we still need to use C syntax with 0xff  */
      write_dollar_variable (yylval.sval);
      c = tokstart[namelen];
      tokstart[namelen] = 0;
      intvar = lookup_only_internalvar (++tokstart);
      --tokstart;
      tokstart[namelen] = c;
      free (uptokstart);
      DUMP_CURRENT_TYPE ("returning VARIABLE");
      return VARIABLE;
    }

  /* Use token-type BLOCKNAME for symbols that happen to be defined as
     functions or symtabs.  If this is not so, then ...
     Use token-type TYPENAME for symbols that happen to be defined
     currently as names of types; NAME for other symbols.
     The caller is not constrained to care about the distinction.  */
  {
    char *tmp = copy_name (yylval.sval);
    struct symbol *sym;
    int is_a_field_of_this = 0;
#if 0 /* EMBARCADERO Local: method call support. */
    int is_a_field = 0;
#endif /* 0 */
    int hextype;


#if 0 /* EMBARCADERO Local: method call support. */
    if (search_field && current_type)
      is_a_field = (lookup_struct_elt_type (current_type, tmp, 1) != NULL);
    if (is_a_field || in_parse_field)
      sym = NULL;
    else
#endif /* 0 */
      sym = lookup_symbol (tmp, expression_context_block,
			   VAR_DOMAIN, &is_a_field_of_this);
    /* EMBARCADERO Local: begin self/frameptr member access. */
    if (!sym && !is_a_field_of_this && !current_type)
      {
        sym = lookup_symbol ("self", expression_context_block,
			     VAR_DOMAIN,
			     &is_a_field_of_this);
        if (sym && sym->type)
          {
	    struct type *domain_type = sym->type;
	    while (TYPE_CODE (domain_type) == TYPE_CODE_PTR)
	      /* Dereference the object. */ 
	      domain_type = TYPE_TARGET_TYPE (domain_type);
	    is_a_field_of_this = (lookup_struct_elt_type (domain_type, tmp, 1) != NULL);	
	    if (!is_a_field_of_this)
	      is_a_field_of_this = (lookup_struct_elt_fn_field (domain_type, tmp, 0) != NULL);
	    if (!is_a_field_of_this)
	      is_a_field_of_this = (lookup_struct_elt_prop_field (domain_type, tmp) != NULL);
	  }
	sym = 0;
      }
    /* EMBARCADERO Local: end self/frameptr member access. */
#if 0 /* EMBARCADERO Local: Lookups are case insensitive. */
    /* second chance uppercased (as Free Pascal does).  */
    if (!sym && !is_a_field_of_this && !is_a_field)
      {
       for (i = 0; i <= namelen; i++)
         {
           if ((tmp[i] >= 'a' && tmp[i] <= 'z'))
             tmp[i] -= ('a'-'A');
         }
       if (search_field && current_type)
	 is_a_field = (lookup_struct_elt_type (current_type, tmp, 1) != NULL);
       if (is_a_field || in_parse_field)
	 sym = NULL;
       else
	 sym = lookup_symbol (tmp, expression_context_block,
			      VAR_DOMAIN, &is_a_field_of_this);
       if (sym || is_a_field_of_this || is_a_field)
         for (i = 0; i <= namelen; i++)
           {
             if ((tokstart[i] >= 'a' && tokstart[i] <= 'z'))
               tokstart[i] -= ('a'-'A');
           }
      }
    /* Third chance Capitalized (as GPC does).  */
    if (!sym && !is_a_field_of_this && !is_a_field)
      {
       for (i = 0; i <= namelen; i++)
         {
           if (i == 0)
             {
              if ((tmp[i] >= 'a' && tmp[i] <= 'z'))
                tmp[i] -= ('a'-'A');
             }
           else
           if ((tmp[i] >= 'A' && tmp[i] <= 'Z'))
             tmp[i] -= ('A'-'a');
          }
       if (search_field && current_type)
	 is_a_field = (lookup_struct_elt_type (current_type, tmp, 1) != NULL);
       if (is_a_field || in_parse_field)
	 sym = NULL;
       else
	 sym = lookup_symbol (tmp, expression_context_block,
			      VAR_DOMAIN, &is_a_field_of_this);
       if (sym || is_a_field_of_this || is_a_field)
          for (i = 0; i <= namelen; i++)
            {
              if (i == 0)
                {
                  if ((tokstart[i] >= 'a' && tokstart[i] <= 'z'))
                    tokstart[i] -= ('a'-'A');
                }
              else
                if ((tokstart[i] >= 'A' && tokstart[i] <= 'Z'))
                  tokstart[i] -= ('A'-'a');
            }
      }

    if (is_a_field ||
        /* EMBARCADERO Local: method call support. */
	search_field && current_type)
      {
        /* EMBARCADERO Local: begin method call support. */
	if (tokstart[namelen] == '(')
	  {
	    /* Collect method arguments as well. */
	    int nest = 1;
	    for (i = namelen+1; tokstart[i]; ++i)
	      {
		if (tokstart[i] == ')')
		  {
		    nest--;
		    if (nest==0)
		      {
			namelen = i + 1;
			break;
		      }
		  }
		if (tokstart[i] == '(')
		    nest++;
	      }
	  }
        /* EMBARCADERO Local: end method call support. */
	tempbuf = (char *) realloc (tempbuf, namelen + 1);
	strncpy (tempbuf, tokstart, namelen); tempbuf [namelen] = 0;
	yylval.sval.ptr = tempbuf;
	yylval.sval.length = namelen;
	free (uptokstart);
	DUMP_CURRENT_TYPE ("returning FIELDNAME");
	return FIELDNAME;
      }
#endif /* 0 */
    /* EMBARCADERO LOCAL begin Delphi units/namespaces */
    /* Try looking in any imported namespaces.  */
    if (!sym && !is_a_field_of_this)
      {
	sym = cp_lookup_symbol_nonlocal (tmp,
					 expression_context_block,
					 VAR_DOMAIN);
      }
    /* EMBARCADERO LOCAL end Delphi units/namespaces */
    /* Call lookup_symtab, not lookup_partial_symtab, in case there are
       no psymtabs (coff, xcoff, or some future change to blow away the
       psymtabs once once symbols are read).  */
    /* EMBARCADERO LOCAL But don't try to lookup the string as a symtab if
       we already have a type we are completing, otherwise, if we have
       a file named "typeinfo", we will think "TypeInfo" in "v.TypeInfo.Kind"
       refers to a symtab instead of a field.  */
    if ((sym && SYMBOL_CLASS (sym) == LOC_BLOCK)
	/* EMBARCADERO LOCAL don't look for a symtab if we have a current_type */
        || (!current_type && lookup_symtab (tmp)))
      {
	yylval.ssym.sym = sym;
	yylval.ssym.is_a_field_of_this = is_a_field_of_this;
	free (uptokstart);
	DUMP_CURRENT_TYPE ("returning BLOCKNAME");
	return BLOCKNAME;
      }
    if (sym && SYMBOL_CLASS (sym) == LOC_TYPEDEF)
        {
#if 1
	  /* Despite the following flaw, we need to keep this code enabled.
	     Because we can get called from check_stub_method, if we don't
	     handle nested types then it screws many operations in any
	     program which uses nested types.  */
	  /* In "A::x", if x is a member function of A and there happens
	     to be a type (nested or not, since the stabs don't make that
	     distinction) named x, then this code incorrectly thinks we
	     are dealing with nested types rather than a member function.  */

	  char *p;
	  char *namestart;
	  struct symbol *best_sym;

	  /* Look ahead to detect nested types.  This probably should be
	     done in the grammar, but trying seemed to introduce a lot
	     of shift/reduce and reduce/reduce conflicts.  It's possible
	     that it could be done, though.  Or perhaps a non-grammar, but
	     less ad hoc, approach would work well.  */

	  /* Since we do not currently have any way of distinguishing
	     a nested type from a non-nested one (the stabs don't tell
	     us whether a type is nested), we just ignore the
	     containing type.  */

	  p = lexptr;
	  best_sym = sym;
	  while (1)
	    {
	      /* Skip whitespace.  */
	      while (*p == ' ' || *p == '\t' || *p == '\n')
		++p;
	      if ((*p == ':' && p[1] == ':')
		  /* EMBARCADERO LOCAL Delphi units/namespaces */
		  || *p == '.')
		{
		  /* EMBARCADERO LOCAL begin Delphi units/namespaces */
		  const char *nsop = (*p == '.') ? "." : "::";
		  /* Skip the `::' (or `.').  */
		  p += strlen (nsop);
		  /* EMBARCADERO LOCAL end Delphi units/namespaces */
		  /* Skip whitespace.  */
		  while (*p == ' ' || *p == '\t' || *p == '\n')
		    ++p;
		  namestart = p;
		  while (*p == '_' || *p == '$' || (*p >= '0' && *p <= '9')
			 || (*p >= 'a' && *p <= 'z')
			 || (*p >= 'A' && *p <= 'Z'))
		    ++p;
		  if (p != namestart)
		    {
		      struct symbol *cur_sym;
		      /* As big as the whole rest of the expression, which is
			 at least big enough.  */
		      char *ncopy = alloca (strlen (tmp)+strlen (namestart)+3);
		      char *tmp1;

		      tmp1 = ncopy;
		      memcpy (tmp1, tmp, strlen (tmp));
		      tmp1 += strlen (tmp);
		      /* EMBARCADERO LOCAL begin Delphi units/namespaces */
		      memcpy (tmp1, nsop, 2);
		      tmp1 += strlen (nsop);;
		      /* EMBARCADERO LOCAL begin Delphi units/namespaces */
		      memcpy (tmp1, namestart, p - namestart);
		      tmp1[p - namestart] = '\0';
		      cur_sym = lookup_symbol (ncopy, expression_context_block,
					       VAR_DOMAIN, (int *) NULL);
		      if (cur_sym)
			{
			  if (SYMBOL_CLASS (cur_sym) == LOC_TYPEDEF)
			    {
			      best_sym = cur_sym;
			      lexptr = p;
			    }
			  else
			    break;
			}
		      else
			break;
		    }
		  else
		    break;
		}
	      else
		break;
	    }

	  yylval.tsym.type = SYMBOL_TYPE (best_sym);
#else /* not 0 */
	  yylval.tsym.type = SYMBOL_TYPE (sym);
#endif /* not 0 */
	  free (uptokstart);
	  DUMP_CURRENT_TYPE ("returning TYPENAME");
	  DUMP_TTYPE ("returning TYPENAME", &yylval.tsym);
	  return TYPENAME;
        }
    yylval.tsym.type
      = language_lookup_primitive_type_by_name (parse_language,
						parse_gdbarch, tmp);
    if (yylval.tsym.type != NULL)
      {
	free (uptokstart);
	DUMP_CURRENT_TYPE ("returning TYPENAME#2");
	DUMP_TTYPE ("returning TYPENAME#2", &yylval.tsym);
	return TYPENAME;
      }

    /* Input names that aren't symbols but ARE valid hex numbers,
       when the input radix permits them, can be names or numbers
       depending on the parse.  Note we support radixes > 16 here.  */
    if (!sym
        && ((tokstart[0] >= 'a' && tokstart[0] < 'a' + input_radix - 10)
            || (tokstart[0] >= 'A' && tokstart[0] < 'A' + input_radix - 10)))
      {
 	YYSTYPE newlval;	/* Its value is ignored.  */
	hextype = parse_number (tokstart, namelen, 0, &newlval);
	if (hextype == INT)
	  {
	    yylval.ssym.sym = sym;
	    yylval.ssym.is_a_field_of_this = is_a_field_of_this;
	    free (uptokstart);
	    DUMP_CURRENT_TYPE ("returning NAME_OR_INT");
	    return NAME_OR_INT;
	  }
      }

    free(uptokstart);
    /* EMBARCADERO Local: begin method call support. */
    if (!sym && current_type)
      {
	tempbuf = (char *) realloc (tempbuf, namelen + 1);
	strncpy (tempbuf, tokstart, namelen); tempbuf [namelen] = 0;
	yylval.sval.ptr = tempbuf;
	yylval.sval.length = namelen; 
	DUMP_CURRENT_TYPE ("returning IDENT");
	DUMP_STOKEN ("returning IDENT", &yylval.sval);
	return IDENT;
      }
    /* EMBARCADERO Local: end method call support. */
    /* Any other kind of symbol.  */
    yylval.ssym.sym = sym;
    yylval.ssym.is_a_field_of_this = is_a_field_of_this;
    DUMP_CURRENT_TYPE ("returning NAME");
    DUMP_SYMTOKEN ("returning NAME", &yylval.ssym);
    return NAME;
  }
}

void
yyerror (msg)
     char *msg;
{
  if (prev_lexptr)
    lexptr = prev_lexptr;

  error (_("A %s in expression, near `%s'."), (msg ? msg : "error"), lexptr);
}
