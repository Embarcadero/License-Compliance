/* YACC parser for C expressions, for GDB.
   Copyright (C) 1986, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997,
   1998, 1999, 2000, 2003, 2004, 2006, 2007, 2008, 2009, 2010, 2011
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

/* Parse a C expression from text in a string,
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
   
%{

#include "defs.h"
#include "gdb_string.h"
#include <ctype.h>
#include "expression.h"
#include "value.h"
#include "parser-defs.h"
#include "language.h"
#include "c-lang.h"
#include "bfd.h" /* Required by objfiles.h.  */
#include "symfile.h" /* Required by objfiles.h.  */
#include "objfiles.h" /* For have_full_symbols and have_partial_symbols */
#include "charset.h"
#include "block.h"
#include "cp-support.h"
#include "dfp.h"
#include "gdb_assert.h"
#include "macroscope.h"

#define parse_type builtin_type (parse_gdbarch)

/* Remap normal yacc parser interface names (yyparse, yylex, yyerror, etc),
   as well as gratuitiously global symbol names, so we can have multiple
   yacc generated parsers in gdb.  Note that these are only the variables
   produced by yacc.  If other parser generators (bison, byacc, etc) produce
   additional global names that conflict at link time, then those parser
   generators need to be fixed instead of adding those names to this list. */

#define	yymaxdepth c_maxdepth
#define	yyparse	c_parse_internal
#define	yylex	c_lex
#define	yyerror	c_error
#define	yylval	c_lval
#define	yychar	c_char
#define	yydebug	c_debug
#define	yypact	c_pact	
#define	yyr1	c_r1			
#define	yyr2	c_r2			
#define	yydef	c_def		
#define	yychk	c_chk		
#define	yypgo	c_pgo		
#define	yyact	c_act		
#define	yyexca	c_exca
#define yyerrflag c_errflag
#define yynerrs	c_nerrs
#define	yyps	c_ps
#define	yypv	c_pv
#define	yys	c_s
#define	yy_yys	c_yys
#define	yystate	c_state
#define	yytmp	c_tmp
#define	yyv	c_v
#define	yy_yyv	c_yyv
#define	yyval	c_val
#define	yylloc	c_lloc
#define yyreds	c_reds		/* With YYDEBUG defined */
#define yytoks	c_toks		/* With YYDEBUG defined */
#define yyname	c_name		/* With YYDEBUG defined */
#define yyrule	c_rule		/* With YYDEBUG defined */
#define yylhs	c_yylhs
#define yylen	c_yylen
#define yydefred c_yydefred
#define yydgoto	c_yydgoto
#define yysindex c_yysindex
#define yyrindex c_yyrindex
#define yygindex c_yygindex
#define yytable	 c_yytable
#define yycheck	 c_yycheck

#ifndef YYDEBUG
#define	YYDEBUG 1		/* Default to yydebug support */
#endif

#define YYFPRINTF parser_fprintf

int yyparse (void);

static int yylex (void);

void yyerror (char *);

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
    struct {
      gdb_byte val[16];
      struct type *type;
    } typed_val_decfloat;
    struct symbol *sym;
    struct type *tval;
    struct stoken sval;
    struct typed_stoken tsval;
    struct ttype tsym;
    struct symtoken ssym;
    int voidval;
    struct block *bval;
    enum exp_opcode opcode;
    struct internalvar *ivar;

    struct stoken_vector svec;
    struct type **tvec;
    int *ivec;
  }

%{
/* YYSTYPE gets defined by %union */
static int parse_number (char *, int, int, YYSTYPE *);
static struct stoken operator_stoken (const char *);

/* EMBARCADERO LOCAL begin properties */
static struct type *current_type;
static void push_current_type (void);
static void pop_current_type (void);
static struct fn_field *current_method;
static struct prop_field *current_property;
/* EMBARCADERO LOCAL end properties */

/* EMBARCADERO LOCAL begin MS integer literal suffix support (eg. ui32) */
enum literal_suffix_kind
  {
    LIT_SUFFIX_NONE,
    LIT_SUFFIX_MS_UNSIGNED_INT,
    LIT_SUFFIX_MS_INT,
    LIT_SUFFIX_C_UNSIGNED_INT,
    LIT_SUFFIX_C_INT
  };
/* EMBARCADERO LOCAL end MS integer literal suffix support (eg. ui32) */
%}

%type <voidval> exp exp1 type_exp start variable qualified_name lcurly
%type <lval> rcurly
%type <tval> type typebase
%type <tvec> nonempty_typelist
/* %type <bval> block */

/* Fancy type parsing.  */
%type <voidval> func_mod direct_abs_decl abs_decl
%type <tval> ptype
%type <lval> array_mod

%token <typed_val_int> INT
%token <typed_val_float> FLOAT
%token <typed_val_decfloat> DECFLOAT

/* Both NAME and TYPENAME tokens represent symbols in the input,
   and both convey their data as strings.
   But a TYPENAME is a string that happens to be defined as a typedef
   or builtin type name (such as int or char)
   and a NAME is any other symbol.
   Contexts where this distinction is not important can use the
   nonterminal "name", which matches either NAME or TYPENAME.  */

%token <tsval> STRING
%token <tsval> CHAR
%token <ssym> NAME /* BLOCKNAME defined below to give it higher precedence. */
%token <ssym> UNKNOWN_CPP_NAME
%token <voidval> COMPLETE
%token <tsym> TYPENAME
%type <sval> name
%type <svec> string_exp
%type <ssym> name_not_typename
%type <tsym> typename

/* A NAME_OR_INT is a symbol which is not known in the symbol table,
   but which would parse as a valid number in the current input radix.
   E.g. "c" when input_radix==16.  Depending on the parse, it will be
   turned into a name or into a number.  */

%token <ssym> NAME_OR_INT 

%token OPERATOR
%token STRUCT CLASS UNION ENUM SIZEOF UNSIGNED COLONCOLON
%token TEMPLATE
%token ERROR
%token NEW DELETE
%type <sval> operator
%token REINTERPRET_CAST DYNAMIC_CAST STATIC_CAST CONST_CAST

/* Special type cases, put in to allow the parser to distinguish different
   legal basetypes.  */
%token SIGNED_KEYWORD LONG SHORT INT_KEYWORD CONST_KEYWORD VOLATILE_KEYWORD DOUBLE_KEYWORD
/* EMBARCADERO LOCAL MS built-in integer types (__int32, etc) */
%token MS_INT8 MS_INT16 MS_INT32 MS_INT64

%token <sval> VARIABLE

%token <opcode> ASSIGN_MODIFY

/* C++ */
%token THIS
%token TRUEKEYWORD
%token FALSEKEYWORD


%left ','
%left ABOVE_COMMA
%right '=' ASSIGN_MODIFY
%right '?'
%left OROR
%left ANDAND
%left '|'
%left '^'
%left '&'
%left EQUAL NOTEQUAL
%left '<' '>' LEQ GEQ
%left LSH RSH
%left '@'
%left '+' '-'
%left '*' '/' '%'
%right UNARY INCREMENT DECREMENT
%right ARROW ARROW_STAR '.' DOT_STAR '[' '('
%token <ssym> BLOCKNAME 
%token <bval> FILENAME
%type <bval> block
%left COLONCOLON


%%

start   :	{ current_type = NULL;
    		  current_method = 0;
		  current_property = 0;
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
			  current_type = $1; }
	;

/* Expressions, including the comma operator.  */
exp1	:	exp
	|	exp1 ',' exp
			{ write_exp_elt_opcode (BINOP_COMMA); }
	;

/* Expressions, not including the comma operator.  */
exp	:	'*' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_IND);
			  /* EMBARCADERO LOCAL properties */
			  if (current_type) 
			    current_type = TYPE_TARGET_TYPE (current_type); }
	;

exp	:	'&' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_ADDR);
			  /* EMBARCADERO LOCAL properties */
			  if (current_type)
			    current_type = TYPE_POINTER_TYPE (current_type); }
	;

exp	:	'-' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_NEG); }
	;

exp	:	'+' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_PLUS); }
	;

exp	:	'!' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_LOGICAL_NOT); }
	;

exp	:	'~' exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_COMPLEMENT); }
	;

exp	:	INCREMENT exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_PREINCREMENT); }
	;

exp	:	DECREMENT exp    %prec UNARY
			{ write_exp_elt_opcode (UNOP_PREDECREMENT); }
	;

exp	:	exp INCREMENT    %prec UNARY
			{ write_exp_elt_opcode (UNOP_POSTINCREMENT); }
	;

exp	:	exp DECREMENT    %prec UNARY
			{ write_exp_elt_opcode (UNOP_POSTDECREMENT); }
	;

exp	:	SIZEOF exp       %prec UNARY
			{ write_exp_elt_opcode (UNOP_SIZEOF); }
	;

exp	:	exp ARROW name
			{ /* EMBARCADERO LOCAL begin properties */
			  current_method = 0;
			  current_property = 0;
			  if (current_type)
			    { if (TYPE_CODE (current_type) == TYPE_CODE_PTR)
			        /* Dereference the object. */ 
				current_type = TYPE_TARGET_TYPE (current_type);
			      current_method = lookup_struct_elt_fn_field (
                                current_type, $3.ptr, 0);
                              if (!current_method)
				current_property = lookup_struct_elt_prop_field (
				  current_type, copy_name ($3));
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
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_PTR);
                              /* Reset the type to the type of the field. */
                              current_type = current_property->type;
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
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      start_arglist ();
			      write_exp_elt_opcode (OP_FUNCALL);
			      write_exp_elt_longcst ((LONGEST) end_arglist ());
			      write_exp_elt_opcode (OP_FUNCALL); 
                              /* Reset the type to the type of the property. */
                              current_type = current_property->type;
                              current_property = 0;
			    }
			  else if (current_property)
			    { error (_("Property \"%s\" not readable."),
				     copy_name ($3));
			      current_property = 0;
			    }
			  /* EMBARCADERO LOCAL end properties */
			  else
			    { write_exp_elt_opcode (STRUCTOP_PTR);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_PTR);
			      /* EMBARCADERO LOCAL begin properties */
                              /* If it's a method, reset the type to the
				 return type of the method, else reset the
				 type to the type of the field. */
			      if (current_method)
				{ current_type = TYPE_TARGET_TYPE (
				    current_method->type);
				  current_method = 0;
				}
			      else if (current_type)
                                current_type = lookup_struct_elt_type (
                                  current_type, copy_name ($3), 1);
			      /* EMBARCADERO LOCAL end properties */
			    }
			}
	;

exp	:	exp ARROW name COMPLETE
			{ mark_struct_expression ();
			  write_exp_elt_opcode (STRUCTOP_PTR);
			  write_exp_string ($3);
			  write_exp_elt_opcode (STRUCTOP_PTR); }
	;

exp	:	exp ARROW COMPLETE
			{ struct stoken s;
			  mark_struct_expression ();
			  write_exp_elt_opcode (STRUCTOP_PTR);
			  s.ptr = "";
			  s.length = 0;
			  write_exp_string (s);
			  write_exp_elt_opcode (STRUCTOP_PTR); }
	;

exp	:	exp ARROW qualified_name
			{ /* exp->type::name becomes exp->*(&type::name) */
			  /* Note: this doesn't work if name is a
			     static member!  FIXME */
			  write_exp_elt_opcode (UNOP_ADDR);
			  write_exp_elt_opcode (STRUCTOP_MPTR); }
	;

exp	:	exp ARROW_STAR exp
			{ write_exp_elt_opcode (STRUCTOP_MPTR); }
	;

exp	:	exp '.' name
			{ /* EMBARCADERO LOCAL begin properties */
			  current_method = 0;
			  current_property = 0;
			  if (current_type)
			    { current_method = lookup_struct_elt_fn_field (
                                current_type, $3.ptr, 0);
                              if (!current_method)
				current_property = lookup_struct_elt_prop_field (
				  current_type, copy_name ($3));
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
                              /* Reset the type to the type of the field. */
                              current_type = current_property->type;
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
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      start_arglist ();
			      write_exp_elt_opcode (OP_FUNCALL);
			      write_exp_elt_longcst ((LONGEST) end_arglist ());
			      write_exp_elt_opcode (OP_FUNCALL); 
                              /* Reset the type to the type of the property. */
                              current_type = current_property->type;
                              current_property = 0;
			    }
			  else if (current_property)
			    { error (_("Property \"%s\" not readable."),
				     copy_name ($3));
			      current_property = 0;
			    }
			  else
			    { write_exp_elt_opcode (STRUCTOP_STRUCT);
			      write_exp_string ($3);
			      write_exp_elt_opcode (STRUCTOP_STRUCT);
			      /* EMBARCADERO LOCAL begin properties */
                              /* If it's a method, reset the type to the
				 return type of the method, else reset the
				 type to the type of the field. */
			      if (current_method)
				{ current_type = TYPE_TARGET_TYPE (
				    current_method->type);
				  current_method = 0;
				}
			      else if (current_type)
                                current_type = lookup_struct_elt_type (
                                  current_type, copy_name ($3), 1);
			      /* EMBARCADERO LOCAL end properties */
			    }
			  /* EMBARCADERO LOCAL end properties */
                        }
	;

exp	:	exp '.' name COMPLETE
			{ mark_struct_expression ();
			  write_exp_elt_opcode (STRUCTOP_STRUCT);
			  write_exp_string ($3);
			  write_exp_elt_opcode (STRUCTOP_STRUCT); }
	;

exp	:	exp '.' COMPLETE
			{ struct stoken s;
			  mark_struct_expression ();
			  write_exp_elt_opcode (STRUCTOP_STRUCT);
			  s.ptr = "";
			  s.length = 0;
			  write_exp_string (s);
			  write_exp_elt_opcode (STRUCTOP_STRUCT); }
	;

exp	:	exp '.' qualified_name
			{ /* exp.type::name becomes exp.*(&type::name) */
			  /* Note: this doesn't work if name is a
			     static member!  FIXME */
			  write_exp_elt_opcode (UNOP_ADDR);
			  write_exp_elt_opcode (STRUCTOP_MEMBER); }
	;

exp	:	exp DOT_STAR exp
			{ write_exp_elt_opcode (STRUCTOP_MEMBER); }
	;

exp	:	exp '[' exp1 ']'
			{ write_exp_elt_opcode (BINOP_SUBSCRIPT);
			  /* EMBARCADERO LOCAL properties */
			  /* Set current_type to the element type.
			     FIXME: need to push/pop current_type around exp1,
			     but that would break parsing.  */
			  if (current_type) 
			    current_type = TYPE_TARGET_TYPE (current_type); }
	;

exp	:	exp '(' 
			/* This is to save the value of arglist_len
			   being accumulated by an outer function call.  */
			{ /* EMBARCADERO LOCAL properties */
			  push_current_type ();
			  start_arglist (); }
		arglist ')'	%prec ARROW
			{ write_exp_elt_opcode (OP_FUNCALL);
			  write_exp_elt_longcst ((LONGEST) end_arglist ());
			  write_exp_elt_opcode (OP_FUNCALL);
			  /* EMBARCADERO LOCAL properties */
			  pop_current_type ();
			  if (current_type)
			    current_type = TYPE_TARGET_TYPE (current_type);
			}
	;

exp	:	UNKNOWN_CPP_NAME '('
			{
			  /* This could potentially be a an argument defined
			     lookup function (Koenig).  */
			  write_exp_elt_opcode (OP_ADL_FUNC);
			  write_exp_elt_block (expression_context_block);
			  write_exp_elt_sym (NULL); /* Placeholder.  */
			  write_exp_string ($1.stoken);
			  write_exp_elt_opcode (OP_ADL_FUNC);

			/* This is to save the value of arglist_len
			   being accumulated by an outer function call.  */

			  start_arglist ();
			}
		arglist ')'	%prec ARROW
			{
			  write_exp_elt_opcode (OP_FUNCALL);
			  write_exp_elt_longcst ((LONGEST) end_arglist ());
			  write_exp_elt_opcode (OP_FUNCALL);
			}
	;

lcurly	:	'{'
			{ start_arglist (); }
	;

arglist	:
	;

arglist	:	exp
			{ arglist_len = 1; }
	;

arglist	:	arglist ',' exp   %prec ABOVE_COMMA
			{ arglist_len++; }
	;

exp     :       exp '(' nonempty_typelist ')' const_or_volatile
			{ int i;
			  write_exp_elt_opcode (TYPE_INSTANCE);
			  write_exp_elt_longcst ((LONGEST) $<ivec>3[0]);
			  for (i = 0; i < $<ivec>3[0]; ++i)
			    write_exp_elt_type ($<tvec>3[i + 1]);
			  write_exp_elt_longcst((LONGEST) $<ivec>3[0]);
			  write_exp_elt_opcode (TYPE_INSTANCE);
			  free ($3);
			}
	;

rcurly	:	'}'
			{ $$ = end_arglist () - 1; }
	;
exp	:	lcurly arglist rcurly	%prec ARROW
			{ write_exp_elt_opcode (OP_ARRAY);
			  write_exp_elt_longcst ((LONGEST) 0);
			  write_exp_elt_longcst ((LONGEST) $3);
			  write_exp_elt_opcode (OP_ARRAY); }
	;

exp	:	lcurly type rcurly exp  %prec UNARY
			{ write_exp_elt_opcode (UNOP_MEMVAL);
			  write_exp_elt_type ($2);
			  write_exp_elt_opcode (UNOP_MEMVAL); }
	;

exp	:	'(' type ')' exp  %prec UNARY
			{ write_exp_elt_opcode (UNOP_CAST);
			  write_exp_elt_type ($2);
			  write_exp_elt_opcode (UNOP_CAST);
			  /* EMBARCADERO LOCAL properties */
			  current_type = $2; }
	;

exp	:	'(' exp1 ')'
			{ }
	;

/* Binary operators in order of decreasing precedence.  */

exp	:	exp '@' exp
			{ write_exp_elt_opcode (BINOP_REPEAT); }
	;

exp	:	exp '*' exp
			{ write_exp_elt_opcode (BINOP_MUL); }
	;

exp	:	exp '/' exp
			{ write_exp_elt_opcode (BINOP_DIV); }
	;

exp	:	exp '%' exp
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

exp	:	exp EQUAL exp
			{ write_exp_elt_opcode (BINOP_EQUAL); }
	;

exp	:	exp NOTEQUAL exp
			{ write_exp_elt_opcode (BINOP_NOTEQUAL); }
	;

exp	:	exp LEQ exp
			{ write_exp_elt_opcode (BINOP_LEQ); }
	;

exp	:	exp GEQ exp
			{ write_exp_elt_opcode (BINOP_GEQ); }
	;

exp	:	exp '<' exp
			{ write_exp_elt_opcode (BINOP_LESS); }
	;

exp	:	exp '>' exp
			{ write_exp_elt_opcode (BINOP_GTR); }
	;

exp	:	exp '&' exp
			{ write_exp_elt_opcode (BINOP_BITWISE_AND); }
	;

exp	:	exp '^' exp
			{ write_exp_elt_opcode (BINOP_BITWISE_XOR); }
	;

exp	:	exp '|' exp
			{ write_exp_elt_opcode (BINOP_BITWISE_IOR); }
	;

exp	:	exp ANDAND exp
			{ write_exp_elt_opcode (BINOP_LOGICAL_AND); }
	;

exp	:	exp OROR exp
			{ write_exp_elt_opcode (BINOP_LOGICAL_OR); }
	;

exp	:	exp '?' exp ':' exp	%prec '?'
			{ write_exp_elt_opcode (TERNOP_COND); }
	;
			  
exp	:	exp '=' exp
			{ write_exp_elt_opcode (BINOP_ASSIGN); }
	;

exp	:	exp ASSIGN_MODIFY exp
			{ write_exp_elt_opcode (BINOP_ASSIGN_MODIFY);
			  write_exp_elt_opcode ($2);
			  write_exp_elt_opcode (BINOP_ASSIGN_MODIFY); }
	;

exp	:	INT
			{ write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type ($1.type);
			  write_exp_elt_longcst ((LONGEST)($1.val));
			  write_exp_elt_opcode (OP_LONG); }
	;

exp	:	CHAR
			{
			  struct stoken_vector vec;
			  vec.len = 1;
			  vec.tokens = &$1;
			  write_exp_string_vector ($1.type, &vec);
			}
	;

exp	:	NAME_OR_INT
			{ YYSTYPE val;
			  parse_number ($1.stoken.ptr, $1.stoken.length, 0, &val);
			  write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (val.typed_val_int.type);
			  write_exp_elt_longcst ((LONGEST)val.typed_val_int.val);
			  write_exp_elt_opcode (OP_LONG);
			}
	;


exp	:	FLOAT
			{ write_exp_elt_opcode (OP_DOUBLE);
			  write_exp_elt_type ($1.type);
			  write_exp_elt_dblcst ($1.dval);
			  write_exp_elt_opcode (OP_DOUBLE); }
	;

exp	:	DECFLOAT
			{ write_exp_elt_opcode (OP_DECFLOAT);
			  write_exp_elt_type ($1.type);
			  write_exp_elt_decfloatcst ($1.val);
			  write_exp_elt_opcode (OP_DECFLOAT); }
	;

exp	:	variable
	;

exp	:	VARIABLE
			{
			  write_dollar_variable ($1);
			}
	;

exp	:	SIZEOF '(' type ')'	%prec UNARY
			{ write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (lookup_signed_typename
					      (parse_language, parse_gdbarch,
					       "int"));
			  CHECK_TYPEDEF ($3);
			  write_exp_elt_longcst ((LONGEST) TYPE_LENGTH ($3));
			  write_exp_elt_opcode (OP_LONG); }
	;

exp	:	REINTERPRET_CAST '<' type '>' '(' exp ')' %prec UNARY
			{ write_exp_elt_opcode (UNOP_REINTERPRET_CAST);
			  write_exp_elt_type ($3);
			  write_exp_elt_opcode (UNOP_REINTERPRET_CAST); }
	;

exp	:	STATIC_CAST '<' type '>' '(' exp ')' %prec UNARY
			{ write_exp_elt_opcode (UNOP_CAST);
			  write_exp_elt_type ($3);
			  write_exp_elt_opcode (UNOP_CAST); }
	;

exp	:	DYNAMIC_CAST '<' type '>' '(' exp ')' %prec UNARY
			{ write_exp_elt_opcode (UNOP_DYNAMIC_CAST);
			  write_exp_elt_type ($3);
			  write_exp_elt_opcode (UNOP_DYNAMIC_CAST); }
	;

exp	:	CONST_CAST '<' type '>' '(' exp ')' %prec UNARY
			{ /* We could do more error checking here, but
			     it doesn't seem worthwhile.  */
			  write_exp_elt_opcode (UNOP_CAST);
			  write_exp_elt_type ($3);
			  write_exp_elt_opcode (UNOP_CAST); }
	;

string_exp:
		STRING
			{
			  /* We copy the string here, and not in the
			     lexer, to guarantee that we do not leak a
			     string.  Note that we follow the
			     NUL-termination convention of the
			     lexer.  */
			  struct typed_stoken *vec = XNEW (struct typed_stoken);
			  $$.len = 1;
			  $$.tokens = vec;

			  vec->type = $1.type;
			  vec->length = $1.length;
			  vec->ptr = malloc ($1.length + 1);
			  memcpy (vec->ptr, $1.ptr, $1.length + 1);
			}

	|	string_exp STRING
			{
			  /* Note that we NUL-terminate here, but just
			     for convenience.  */
			  char *p;
			  ++$$.len;
			  $$.tokens = realloc ($$.tokens,
					       $$.len * sizeof (struct typed_stoken));

			  p = malloc ($2.length + 1);
			  memcpy (p, $2.ptr, $2.length + 1);

			  $$.tokens[$$.len - 1].type = $2.type;
			  $$.tokens[$$.len - 1].length = $2.length;
			  $$.tokens[$$.len - 1].ptr = p;
			}
		;

exp	:	string_exp
			{
			  int i;
			  enum c_string_type type = C_STRING;

			  for (i = 0; i < $1.len; ++i)
			    {
			      switch ($1.tokens[i].type)
				{
				case C_STRING:
				  break;
				case C_WIDE_STRING:
				case C_STRING_16:
				case C_STRING_32:
				  if (type != C_STRING
				      && type != $1.tokens[i].type)
				    error (_("Undefined string concatenation."));
				  type = $1.tokens[i].type;
				  break;
				default:
				  /* internal error */
				  internal_error (__FILE__, __LINE__,
						  "unrecognized type in string concatenation");
				}
			    }

			  write_exp_string_vector (type, &$1);
			  for (i = 0; i < $1.len; ++i)
			    free ($1.tokens[i].ptr);
			  free ($1.tokens);
			}
	;

/* C++.  */
/* EMBARCADERO LOCAL begin properties */
exp	:	THIS
			{ 
			  struct value * this_val;
			  struct type * this_type;
			  write_exp_elt_opcode (OP_THIS);
			  write_exp_elt_opcode (OP_THIS); 
			  /* we need type of this */
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
			}
	;
/* EMBARCADERO LOCAL end properties */

exp     :       TRUEKEYWORD    
                        { write_exp_elt_opcode (OP_LONG);
                          write_exp_elt_type (parse_type->builtin_bool);
                          write_exp_elt_longcst ((LONGEST) 1);
                          write_exp_elt_opcode (OP_LONG); }
	;

exp     :       FALSEKEYWORD   
                        { write_exp_elt_opcode (OP_LONG);
                          write_exp_elt_type (parse_type->builtin_bool);
                          write_exp_elt_longcst ((LONGEST) 0);
                          write_exp_elt_opcode (OP_LONG); }
	;

/* end of C++.  */

block	:	BLOCKNAME
			{
			  if ($1.sym)
			    $$ = SYMBOL_BLOCK_VALUE ($1.sym);
			  else
			    error (_("No file or function \"%s\"."),
				   copy_name ($1.stoken));
			}
	|	FILENAME
			{
			  $$ = $1;
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

qualified_name:	TYPENAME COLONCOLON name
			{
			  struct type *type = $1.type;
			  CHECK_TYPEDEF (type);
			  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
			      && TYPE_CODE (type) != TYPE_CODE_UNION
			      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
			    error (_("`%s' is not defined as an aggregate type."),
				   TYPE_NAME (type));

			  write_exp_elt_opcode (OP_SCOPE);
			  write_exp_elt_type (type);
			  write_exp_string ($3);
			  write_exp_elt_opcode (OP_SCOPE);
			}
	|	TYPENAME COLONCOLON '~' name
			{
			  struct type *type = $1.type;
			  struct stoken tmp_token;
			  CHECK_TYPEDEF (type);
			  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
			      && TYPE_CODE (type) != TYPE_CODE_UNION
			      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
			    error (_("`%s' is not defined as an aggregate type."),
				   TYPE_NAME (type));

			  tmp_token.ptr = (char*) alloca ($4.length + 2);
			  tmp_token.length = $4.length + 1;
			  tmp_token.ptr[0] = '~';
			  memcpy (tmp_token.ptr+1, $4.ptr, $4.length);
			  tmp_token.ptr[tmp_token.length] = 0;

			  /* Check for valid destructor name.  */
			  destructor_name_p (tmp_token.ptr, type);
			  write_exp_elt_opcode (OP_SCOPE);
			  write_exp_elt_type (type);
			  write_exp_string (tmp_token);
			  write_exp_elt_opcode (OP_SCOPE);
			}
	|	TYPENAME COLONCOLON name COLONCOLON name
			{
			  char *copy = copy_name ($3);
			  error (_("No type \"%s\" within class "
				   "or namespace \"%s\"."),
				 copy, TYPE_NAME ($1.type));
			}
	;

variable:	qualified_name
	|	COLONCOLON name_not_typename
			{
			  char *name = copy_name ($2.stoken);
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
			  else if (!have_full_symbols () && !have_partial_symbols ())
			    error (_("No symbol table is loaded.  Use the \"file\" command."));
			  else
			    error (_("No symbol \"%s\" in current context."), name);
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
			      /* EMBARCADERO LOCAL properties */
			      current_type = sym->type;
			    }
			  else if ($1.is_a_field_of_this)
			    {
			      struct value * this_val;
			      /* C++: it hangs off of `this'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0
				  || contained_in (block_found,
						   innermost_block))
				innermost_block = block_found;
			      /* EMBARCADERO Local: begin properties. */
			      /* We need type of this */
			      this_val = value_of_this (0); 
			      if (this_val)
				current_type = value_type (this_val);
			      else
				current_type = NULL;
			      /* Try to lookup the field. */
			      if (!current_type ||
				  (lookup_struct_elt_type (
				     current_type,
				     copy_name ($1.stoken), 1) == NULL))
			        {
				  /* Field lookup failed. See if it's a property.  */
				  sym = lookup_symbol ("this", expression_context_block,
						       VAR_DOMAIN,
						       0);
				  if (sym && sym->type)
				    current_type = sym->type;
				  if (!current_type)
				    {
				      /* We shouldn't have gotten here if we
					 couldn't find the "this" type. */
				      error ("\"this\" symbol not found.");
				      goto done_variable;
				    }
			          current_property = lookup_struct_elt_prop_field (
				    current_type, $1.stoken.ptr);
				  if (!current_property)
				    goto do_this_field;
				  /* If property read is just a field, use that field.
				     FIXME: need to support writing! */
				  if (PROP_FIELD_READ_NAME(*current_property) &&
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
				      current_property = 0;
				    }
				  /* If property read is a getter, use that method.
				     FIXME: need to support writing! */
				  else if (PROP_FIELD_READ_NAME(*current_property) &&
					   PROP_FIELD_GETTER(*current_property))
				    { char* prop_read_name =
					PROP_FIELD_READ_NAME(*current_property);
				      $1.stoken.ptr = prop_read_name;
				      $1.stoken.length = strlen(prop_read_name);
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
				      /* Reset the type to the type of the property. */
				      current_type = current_property->type;
				      current_property = 0;
				    }
				  else
				    { error ("Property \"%s\" not readable.",
					     $1.stoken.ptr);
				      current_property = 0;
				      goto done_variable;
				    }
				}
			      /* EMBARCADERO Local: end properties. */
			      else
				{
				do_this_field:
				  /* It's a normal field. */
				  write_exp_elt_opcode (OP_THIS);
				  write_exp_elt_opcode (OP_THIS);
				  write_exp_elt_opcode (STRUCTOP_PTR);
				  write_exp_string ($1.stoken);
				  write_exp_elt_opcode (STRUCTOP_PTR);
				  /* EMBARCADERO Local: properties. */
				  /* Reset the type to the type of the field. */
				  if (current_type)
				    current_type = lookup_struct_elt_type (
				      current_type,
				      copy_name ($1.stoken), 0);
				}
			    }
			  else
			    {
			      struct minimal_symbol *msymbol;
			      char *arg = copy_name ($1.stoken);

			      msymbol =
				lookup_minimal_symbol (arg, NULL, NULL);
			      if (msymbol != NULL)
				write_exp_msymbol (msymbol);
			      else if (!have_full_symbols () && !have_partial_symbols ())
				error (_("No symbol table is loaded.  Use the \"file\" command."));
			      else
				error (_("No symbol \"%s\" in current context."),
				       copy_name ($1.stoken));
			    }
			  done_variable: ;
			}
	;

space_identifier : '@' NAME
		{ push_type_address_space (copy_name ($2.stoken));
		  push_type (tp_space_identifier);
		}
	;

const_or_volatile: const_or_volatile_noopt
	|
	;

cv_with_space_id : const_or_volatile space_identifier const_or_volatile
	;

const_or_volatile_or_space_identifier_noopt: cv_with_space_id
	| const_or_volatile_noopt 
	;

const_or_volatile_or_space_identifier: 
		const_or_volatile_or_space_identifier_noopt
	|
	;

abs_decl:	'*'
			{ push_type (tp_pointer); $$ = 0; }
	|	'*' abs_decl
			{ push_type (tp_pointer); $$ = $2; }
	|	'&'
			{ push_type (tp_reference); $$ = 0; }
	|	'&' abs_decl
			{ push_type (tp_reference); $$ = $2; }
	|	direct_abs_decl
	;

direct_abs_decl: '(' abs_decl ')'
			{ $$ = $2; }
	|	direct_abs_decl array_mod
			{
			  push_type_int ($2);
			  push_type (tp_array);
			}
	|	array_mod
			{
			  push_type_int ($1);
			  push_type (tp_array);
			  $$ = 0;
			}

	| 	direct_abs_decl func_mod
			{ push_type (tp_function); }
	|	func_mod
			{ push_type (tp_function); }
	;

array_mod:	'[' ']'
			{ $$ = -1; }
	|	'[' INT ']'
			{ $$ = $2.val; }
	;

func_mod:	'(' ')'
			{ $$ = 0; }
	|	'(' nonempty_typelist ')'
			{ free ($2); $$ = 0; }
	;

/* We used to try to recognize pointer to member types here, but
   that didn't work (shift/reduce conflicts meant that these rules never
   got executed).  The problem is that
     int (foo::bar::baz::bizzle)
   is a function type but
     int (foo::bar::baz::bizzle::*)
   is a pointer to member type.  Stroustrup loses again!  */

type	:	ptype
	;

typebase  /* Implements (approximately): (type-qualifier)* type-specifier */
	:	TYPENAME
			{ $$ = $1.type; }
	|	INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "int"); }
	|	LONG
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long"); }
	|	SHORT
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "short"); }
	|	LONG INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long"); }
	|	LONG SIGNED_KEYWORD INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long"); }
	|	LONG SIGNED_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long"); }
	|	SIGNED_KEYWORD LONG INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long"); }
	|	UNSIGNED LONG INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long"); }
	|	LONG UNSIGNED INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long"); }
	|	LONG UNSIGNED
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long"); }
	|	LONG LONG
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	LONG LONG INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	LONG LONG SIGNED_KEYWORD INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	LONG LONG SIGNED_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	SIGNED_KEYWORD LONG LONG
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	SIGNED_KEYWORD LONG LONG INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	UNSIGNED LONG LONG
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long long"); }
	|	UNSIGNED LONG LONG INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long long"); }
	|	LONG LONG UNSIGNED
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long long"); }
	|	LONG LONG UNSIGNED INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long long"); }
	|	SHORT INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "short"); }
	|	SHORT SIGNED_KEYWORD INT_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "short"); }
	|	SHORT SIGNED_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "short"); }
	|	UNSIGNED SHORT INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "short"); }
	|	SHORT UNSIGNED 
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "short"); }
	|	SHORT UNSIGNED INT_KEYWORD
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "short"); }
	|	DOUBLE_KEYWORD
			{ $$ = lookup_typename (parse_language, parse_gdbarch,
						"double", (struct block *) NULL,
						0); }
	|	LONG DOUBLE_KEYWORD
			{ $$ = lookup_typename (parse_language, parse_gdbarch,
						"long double",
						(struct block *) NULL, 0); }
	|	STRUCT name
			{ $$ = lookup_struct (copy_name ($2),
					      expression_context_block); }
	|	CLASS name
			{ $$ = lookup_struct (copy_name ($2),
					      expression_context_block); }
	|	UNION name
			{ $$ = lookup_union (copy_name ($2),
					     expression_context_block); }
	|	ENUM name
			{ $$ = lookup_enum (copy_name ($2),
					    expression_context_block); }
	|	UNSIGNED typename
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 TYPE_NAME($2.type)); }
	|	UNSIGNED
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "int"); }
	|	SIGNED_KEYWORD typename
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       TYPE_NAME($2.type)); }
	|	SIGNED_KEYWORD
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "int"); }
		/* EMBARCADERO LOCAL begin MS built-in integer types (__int32, etc) */
	|	MS_INT8
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "char"); }
	|	MS_INT16
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "short"); }
	|	MS_INT32
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "int"); }
	|	MS_INT64
			{ $$ = lookup_signed_typename (parse_language,
						       parse_gdbarch,
						       "long long"); }
	|	UNSIGNED MS_INT8
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "char"); }
	|	UNSIGNED MS_INT16
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "short"); }
	|	UNSIGNED MS_INT32
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "int"); }
	|	UNSIGNED MS_INT64
			{ $$ = lookup_unsigned_typename (parse_language,
							 parse_gdbarch,
							 "long long"); }
		/* EMBARCADERO LOCAL end MS built-in integer types (__int32, etc) */

                /* It appears that this rule for templates is never
                   reduced; template recognition happens by lookahead
                   in the token processing code in yylex. */         
	|	TEMPLATE name '<' type '>'
			{ $$ = lookup_template_type(copy_name($2), $4,
						    expression_context_block);
			}
	| const_or_volatile_or_space_identifier_noopt typebase 
			{ $$ = follow_types ($2); }
	| typebase const_or_volatile_or_space_identifier_noopt 
			{ $$ = follow_types ($1); }
	;

typename:	TYPENAME
	|	INT_KEYWORD
		{
		  $$.stoken.ptr = "int";
		  $$.stoken.length = 3;
		  $$.type = lookup_signed_typename (parse_language,
						    parse_gdbarch,
						    "int");
		}
	|	LONG
		{
		  $$.stoken.ptr = "long";
		  $$.stoken.length = 4;
		  $$.type = lookup_signed_typename (parse_language,
						    parse_gdbarch,
						    "long");
		}
	|	SHORT
		{
		  $$.stoken.ptr = "short";
		  $$.stoken.length = 5;
		  $$.type = lookup_signed_typename (parse_language,
						    parse_gdbarch,
						    "short");
		}
	;

nonempty_typelist
	:	type
		{ $$ = (struct type **) malloc (sizeof (struct type *) * 2);
		  $<ivec>$[0] = 1;	/* Number of types in vector */
		  $$[1] = $1;
		}
	|	nonempty_typelist ',' type
		{ int len = sizeof (struct type *) * (++($<ivec>1[0]) + 1);
		  $$ = (struct type **) realloc ((char *) $1, len);
		  $$[$<ivec>$[0]] = $3;
		}
	;

ptype	:	typebase
	|	ptype const_or_volatile_or_space_identifier abs_decl const_or_volatile_or_space_identifier
		{ $$ = follow_types ($1); }
	;

const_and_volatile: 	CONST_KEYWORD VOLATILE_KEYWORD
	| 		VOLATILE_KEYWORD CONST_KEYWORD
	;

const_or_volatile_noopt:  	const_and_volatile 
			{ push_type (tp_const);
			  push_type (tp_volatile); 
			}
	| 		CONST_KEYWORD
			{ push_type (tp_const); }
	| 		VOLATILE_KEYWORD
			{ push_type (tp_volatile); }
	;

operator:	OPERATOR NEW
			{ $$ = operator_stoken (" new"); }
	|	OPERATOR DELETE
			{ $$ = operator_stoken (" delete"); }
	|	OPERATOR NEW '[' ']'
			{ $$ = operator_stoken (" new[]"); }
	|	OPERATOR DELETE '[' ']'
			{ $$ = operator_stoken (" delete[]"); }
	|	OPERATOR '+'
			{ $$ = operator_stoken ("+"); }
	|	OPERATOR '-'
			{ $$ = operator_stoken ("-"); }
	|	OPERATOR '*'
			{ $$ = operator_stoken ("*"); }
	|	OPERATOR '/'
			{ $$ = operator_stoken ("/"); }
	|	OPERATOR '%'
			{ $$ = operator_stoken ("%"); }
	|	OPERATOR '^'
			{ $$ = operator_stoken ("^"); }
	|	OPERATOR '&'
			{ $$ = operator_stoken ("&"); }
	|	OPERATOR '|'
			{ $$ = operator_stoken ("|"); }
	|	OPERATOR '~'
			{ $$ = operator_stoken ("~"); }
	|	OPERATOR '!'
			{ $$ = operator_stoken ("!"); }
	|	OPERATOR '='
			{ $$ = operator_stoken ("="); }
	|	OPERATOR '<'
			{ $$ = operator_stoken ("<"); }
	|	OPERATOR '>'
			{ $$ = operator_stoken (">"); }
	|	OPERATOR ASSIGN_MODIFY
			{ const char *op = "unknown";
			  switch ($2)
			    {
			    case BINOP_RSH:
			      op = ">>=";
			      break;
			    case BINOP_LSH:
			      op = "<<=";
			      break;
			    case BINOP_ADD:
			      op = "+=";
			      break;
			    case BINOP_SUB:
			      op = "-=";
			      break;
			    case BINOP_MUL:
			      op = "*=";
			      break;
			    case BINOP_DIV:
			      op = "/=";
			      break;
			    case BINOP_REM:
			      op = "%=";
			      break;
			    case BINOP_BITWISE_IOR:
			      op = "|=";
			      break;
			    case BINOP_BITWISE_AND:
			      op = "&=";
			      break;
			    case BINOP_BITWISE_XOR:
			      op = "^=";
			      break;
			    default:
			      break;
			    }

			  $$ = operator_stoken (op);
			}
	|	OPERATOR LSH
			{ $$ = operator_stoken ("<<"); }
	|	OPERATOR RSH
			{ $$ = operator_stoken (">>"); }
	|	OPERATOR EQUAL
			{ $$ = operator_stoken ("=="); }
	|	OPERATOR NOTEQUAL
			{ $$ = operator_stoken ("!="); }
	|	OPERATOR LEQ
			{ $$ = operator_stoken ("<="); }
	|	OPERATOR GEQ
			{ $$ = operator_stoken (">="); }
	|	OPERATOR ANDAND
			{ $$ = operator_stoken ("&&"); }
	|	OPERATOR OROR
			{ $$ = operator_stoken ("||"); }
	|	OPERATOR INCREMENT
			{ $$ = operator_stoken ("++"); }
	|	OPERATOR DECREMENT
			{ $$ = operator_stoken ("--"); }
	|	OPERATOR ','
			{ $$ = operator_stoken (","); }
	|	OPERATOR ARROW_STAR
			{ $$ = operator_stoken ("->*"); }
	|	OPERATOR ARROW
			{ $$ = operator_stoken ("->"); }
	|	OPERATOR '(' ')'
			{ $$ = operator_stoken ("()"); }
	|	OPERATOR '[' ']'
			{ $$ = operator_stoken ("[]"); }
	|	OPERATOR ptype
			{ char *name;
			  long length;
			  struct ui_file *buf = mem_fileopen ();

			  c_print_type ($2, NULL, buf, -1, 0);
			  name = ui_file_xstrdup (buf, &length);
			  ui_file_delete (buf);
			  $$ = operator_stoken (name);
			  free (name);
			}
	;



name	:	NAME { $$ = $1.stoken; }
	|	BLOCKNAME { $$ = $1.stoken; }
	|	TYPENAME { $$ = $1.stoken; }
	|	NAME_OR_INT  { $$ = $1.stoken; }
	|	UNKNOWN_CPP_NAME  { $$ = $1.stoken; }
	|	operator { $$ = $1; }
	;

name_not_typename :	NAME
	|	BLOCKNAME
/* These would be useful if name_not_typename was useful, but it is just
   a fake for "variable", so these cause reduce/reduce conflicts because
   the parser can't tell whether NAME_OR_INT is a name_not_typename (=variable,
   =exp) or just an exp.  If name_not_typename was ever used in an lvalue
   context where only a name could occur, this might be useful.
  	|	NAME_OR_INT
 */
	|	operator
			{
			  $$.stoken = $1;
			  $$.sym = lookup_symbol ($1.ptr,
						  expression_context_block,
						  VAR_DOMAIN,
						  &$$.is_a_field_of_this);
			}
	|	UNKNOWN_CPP_NAME
	;

%%

/* Returns a stoken of the operator name given by OP (which does not
   include the string "operator").  */ 
static struct stoken
operator_stoken (const char *op)
{
  static const char *operator_string = "operator";
  struct stoken st = { NULL, 0 };
  st.length = strlen (operator_string) + strlen (op);
  st.ptr = malloc (st.length + 1);
  strcpy (st.ptr, operator_string);
  strcat (st.ptr, op);

  /* The toplevel (c_parse) will free the memory allocated here.  */
  make_cleanup (free, st.ptr);
  return st;
};

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

  /* EMBARCADERO LOCAL: MS integer literal suffix support (e.g. ui32) */
  /* Set if we have found a "L" or "U" suffix, or an MS integer suffix.  */
  enum literal_suffix_kind suffix_kind = LIT_SUFFIX_NONE;

  ULONGEST high_bit;
  struct type *signed_type;
  struct type *unsigned_type;

  if (parsed_float)
    {
      const char *suffix;
      int suffix_len;

      /* If it ends at "df", "dd" or "dl", take it as type of decimal floating
         point.  Return DECFLOAT.  */

      if (len >= 2 && p[len - 2] == 'd' && p[len - 1] == 'f')
	{
	  p[len - 2] = '\0';
	  putithere->typed_val_decfloat.type
	    = parse_type->builtin_decfloat;
	  decimal_from_string (putithere->typed_val_decfloat.val, 4,
			       gdbarch_byte_order (parse_gdbarch), p);
	  p[len - 2] = 'd';
	  return DECFLOAT;
	}

      if (len >= 2 && p[len - 2] == 'd' && p[len - 1] == 'd')
	{
	  p[len - 2] = '\0';
	  putithere->typed_val_decfloat.type
	    = parse_type->builtin_decdouble;
	  decimal_from_string (putithere->typed_val_decfloat.val, 8,
			       gdbarch_byte_order (parse_gdbarch), p);
	  p[len - 2] = 'd';
	  return DECFLOAT;
	}

      if (len >= 2 && p[len - 2] == 'd' && p[len - 1] == 'l')
	{
	  p[len - 2] = '\0';
	  putithere->typed_val_decfloat.type
	    = parse_type->builtin_declong;
	  decimal_from_string (putithere->typed_val_decfloat.val, 16,
			       gdbarch_byte_order (parse_gdbarch), p);
	  p[len - 2] = 'd';
	  return DECFLOAT;
	}

      if (! parse_c_float (parse_gdbarch, p, len,
			   &putithere->typed_val_float.dval,
			   &putithere->typed_val_float.type))
	return ERROR;
      return FLOAT;
    }

  /* Handle base-switching prefixes 0x, 0t, 0d, 0 */
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

      case 'b':
      case 'B':
	if (len >= 3)
	  {
	    p += 2;
	    base = 2;
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
      if (c != 'l' && c != 'u'
	  /* EMBARCADERO LOCAL: MS integer literal suffix support (eg. ui32) */
	  && c != 'i' && suffix_kind == LIT_SUFFIX_NONE)
	n *= base;
      if (c >= '0' && c <= '9')
	{
	  if (suffix_kind != LIT_SUFFIX_NONE)
	    {
	      /* EMBARCADERO LOCAL: begin MS integer literal suffix support (eg. ui32) */
	      if (suffix_kind == LIT_SUFFIX_MS_INT
		  || suffix_kind == LIT_SUFFIX_MS_UNSIGNED_INT)
		{
		  /* Parse the bits in the MS suffix.  */
		  unsigned int MS_suffix_bits = c - '0';
		  if (p != 0)
		    MS_suffix_bits = MS_suffix_bits * 10 + (*p - '0');
		  switch (MS_suffix_bits) 
		    {
		    case 8:
		      break;
		    case 16:
		    case 32:
		      /* FIXME: what about truncating? */
		      /* fall thru */
		    case 64:
		      if (MS_suffix_bits == 64)
		        long_p = 2;
		      --len;
		      ++p;
		      break;
		    default:
		      /* Invalid bit value for MS integer literal suffix. */
		      return ERROR;    
		    }
		}
	      else
	      /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */
		return ERROR;    
	    }
	  else 
	    n += i = c - '0';
	}
      else
	{
	  if (base > 10 && c >= 'a' && c <= 'f')
	    {
	      if (suffix_kind != LIT_SUFFIX_NONE)
		return ERROR;
	      n += i = c - 'a' + 10;
	    }
	  else if (c == 'l')
	    {
	      /* EMBARCADERO LOCAL: begin MS integer literal suffix support (eg. ui32) */
	      /* 'l' can't follow an MS suffix.  */
	      if (suffix_kind == LIT_SUFFIX_MS_INT
		  || suffix_kind == LIT_SUFFIX_MS_UNSIGNED_INT)
		return ERROR;
	      if (suffix_kind != LIT_SUFFIX_C_UNSIGNED_INT)
		suffix_kind = LIT_SUFFIX_C_INT;
	      ++long_p;
	      /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */
	    }
	  else if (c == 'u')
	    {
	      /* EMBARCADERO LOCAL: begin MS integer literal suffix support (eg. ui32) */
	      /* 'u' can't follow an MS suffix.  */
	      if (suffix_kind == LIT_SUFFIX_MS_INT
		  || suffix_kind == LIT_SUFFIX_MS_UNSIGNED_INT)
		return ERROR;
	      suffix_kind = LIT_SUFFIX_C_UNSIGNED_INT;
	      unsigned_p = 1;
	      /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */
	    }
	  /* EMBARCADERO LOCAL: begin MS integer literal suffix support (eg. ui32) */
	  else if (c == 'i')
	    {
	      if (suffix_kind == LIT_SUFFIX_NONE)
		suffix_kind = LIT_SUFFIX_MS_INT;
	      else if (suffix_kind == LIT_SUFFIX_C_UNSIGNED_INT) /* Did we see a 'u'? */
	        suffix_kind = LIT_SUFFIX_MS_UNSIGNED_INT;
	      else
		return ERROR;	/* Invalid integer literal suffix */
	    }
	  /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */
	  else
	    return ERROR;	/* Char not a digit */
	}
      if (i >= base)
	return ERROR;		/* Invalid digit in this base */

      /* Portably test for overflow (only works for nonzero values, so make
	 a second check for zero).  FIXME: Can't we just make n and prevn
	 unsigned and avoid this?  */
      /* EMBARCADERO LOCAL: begin MS integer literal suffix support (eg. ui32) */
      if (suffix_kind == LIT_SUFFIX_NONE)
	{
	  if (c != 'l' && c != 'u' && c != 'i' && (prevn >= n) && n != 0)
	    unsigned_p = 1;		/* Try something unsigned */

	  /* Portably test for unsigned overflow.
	     FIXME: This check is wrong; for example it doesn't find overflow
	     on 0x123456789 when LONGEST is 32 bits.  */
	  if (c != 'l' && c != 'u' && c != 'i' && n != 0)
	    {	
	      if ((unsigned_p && (ULONGEST) prevn >= (ULONGEST) n))
		error (_("Numeric constant too large."));
	    }
	}
      /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */
      prevn = n;
    }
  /* EMBARCADERO LOCAL: end MS integer literal suffix support (eg. ui32) */

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
      has to be unsigned. */

   /* EMBARCADERO LOCAL: MS integer literal suffix support (eg. ui32) */
   if (unsigned_p || ((n & high_bit) && (suffix_kind != LIT_SUFFIX_MS_INT))) 
     {
       putithere->typed_val_int.type = unsigned_type;
     }
   else 
     {
       putithere->typed_val_int.type = signed_type;
     }

   return INT;
}

/* Temporary obstack used for holding strings.  */
static struct obstack tempbuf;
static int tempbuf_init;

/* Parse a C escape sequence.  The initial backslash of the sequence
   is at (*PTR)[-1].  *PTR will be updated to point to just after the
   last character of the sequence.  If OUTPUT is not NULL, the
   translated form of the escape sequence will be written there.  If
   OUTPUT is NULL, no output is written and the call will only affect
   *PTR.  If an escape sequence is expressed in target bytes, then the
   entire sequence will simply be copied to OUTPUT.  Return 1 if any
   character was emitted, 0 otherwise.  */

int
c_parse_escape (char **ptr, struct obstack *output)
{
  char *tokptr = *ptr;
  int result = 1;

  /* Some escape sequences undergo character set conversion.  Those we
     translate here.  */
  switch (*tokptr)
    {
      /* Hex escapes do not undergo character set conversion, so keep
	 the escape sequence for later.  */
    case 'x':
      if (output)
	obstack_grow_str (output, "\\x");
      ++tokptr;
      if (!isxdigit (*tokptr))
	error (_("\\x escape without a following hex digit"));
      while (isxdigit (*tokptr))
	{
	  if (output)
	    obstack_1grow (output, *tokptr);
	  ++tokptr;
	}
      break;

      /* Octal escapes do not undergo character set conversion, so
	 keep the escape sequence for later.  */
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
      {
	int i;
	if (output)
	  obstack_grow_str (output, "\\");
	for (i = 0;
	     i < 3 && isdigit (*tokptr) && *tokptr != '8' && *tokptr != '9';
	     ++i)
	  {
	    if (output)
	      obstack_1grow (output, *tokptr);
	    ++tokptr;
	  }
      }
      break;

      /* We handle UCNs later.  We could handle them here, but that
	 would mean a spurious error in the case where the UCN could
	 be converted to the target charset but not the host
	 charset.  */
    case 'u':
    case 'U':
      {
	char c = *tokptr;
	int i, len = c == 'U' ? 8 : 4;
	if (output)
	  {
	    obstack_1grow (output, '\\');
	    obstack_1grow (output, *tokptr);
	  }
	++tokptr;
	if (!isxdigit (*tokptr))
	  error (_("\\%c escape without a following hex digit"), c);
	for (i = 0; i < len && isxdigit (*tokptr); ++i)
	  {
	    if (output)
	      obstack_1grow (output, *tokptr);
	    ++tokptr;
	  }
      }
      break;

      /* We must pass backslash through so that it does not
	 cause quoting during the second expansion.  */
    case '\\':
      if (output)
	obstack_grow_str (output, "\\\\");
      ++tokptr;
      break;

      /* Escapes which undergo conversion.  */
    case 'a':
      if (output)
	obstack_1grow (output, '\a');
      ++tokptr;
      break;
    case 'b':
      if (output)
	obstack_1grow (output, '\b');
      ++tokptr;
      break;
    case 'f':
      if (output)
	obstack_1grow (output, '\f');
      ++tokptr;
      break;
    case 'n':
      if (output)
	obstack_1grow (output, '\n');
      ++tokptr;
      break;
    case 'r':
      if (output)
	obstack_1grow (output, '\r');
      ++tokptr;
      break;
    case 't':
      if (output)
	obstack_1grow (output, '\t');
      ++tokptr;
      break;
    case 'v':
      if (output)
	obstack_1grow (output, '\v');
      ++tokptr;
      break;

      /* GCC extension.  */
    case 'e':
      if (output)
	obstack_1grow (output, HOST_ESCAPE_CHAR);
      ++tokptr;
      break;

      /* Backslash-newline expands to nothing at all.  */
    case '\n':
      ++tokptr;
      result = 0;
      break;

      /* A few escapes just expand to the character itself.  */
    case '\'':
    case '\"':
    case '?':
      /* GCC extensions.  */
    case '(':
    case '{':
    case '[':
    case '%':
      /* Unrecognized escapes turn into the character itself.  */
    default:
      if (output)
	obstack_1grow (output, *tokptr);
      ++tokptr;
      break;
    }
  *ptr = tokptr;
  return result;
}

/* Parse a string or character literal from TOKPTR.  The string or
   character may be wide or unicode.  *OUTPTR is set to just after the
   end of the literal in the input string.  The resulting token is
   stored in VALUE.  This returns a token value, either STRING or
   CHAR, depending on what was parsed.  *HOST_CHARS is set to the
   number of host characters in the literal.  */
static int
parse_string_or_char (char *tokptr, char **outptr, struct typed_stoken *value,
		      int *host_chars)
{
  int quote;
  enum c_string_type type;

  /* Build the gdb internal form of the input string in tempbuf.  Note
     that the buffer is null byte terminated *only* for the
     convenience of debugging gdb itself and printing the buffer
     contents when the buffer contains no embedded nulls.  Gdb does
     not depend upon the buffer being null byte terminated, it uses
     the length string instead.  This allows gdb to handle C strings
     (as well as strings in other languages) with embedded null
     bytes */

  if (!tempbuf_init)
    tempbuf_init = 1;
  else
    obstack_free (&tempbuf, NULL);
  obstack_init (&tempbuf);

  /* Record the string type.  */
  if (*tokptr == 'L')
    {
      type = C_WIDE_STRING;
      ++tokptr;
    }
  else if (*tokptr == 'u')
    {
      type = C_STRING_16;
      ++tokptr;
    }
  else if (*tokptr == 'U')
    {
      type = C_STRING_32;
      ++tokptr;
    }
  else
    type = C_STRING;

  /* Skip the quote.  */
  quote = *tokptr;
  if (quote == '\'')
    type |= C_CHAR;
  ++tokptr;

  *host_chars = 0;

  while (*tokptr)
    {
      char c = *tokptr;
      if (c == '\\')
	{
	  ++tokptr;
	  *host_chars += c_parse_escape (&tokptr, &tempbuf);
	}
      else if (c == quote)
	break;
      else
	{
	  obstack_1grow (&tempbuf, c);
	  ++tokptr;
	  /* FIXME: this does the wrong thing with multi-byte host
	     characters.  We could use mbrlen here, but that would
	     make "set host-charset" a bit less useful.  */
	  ++*host_chars;
	}
    }

  if (*tokptr != quote)
    {
      if (quote == '"')
	error (_("Unterminated string in expression."));
      else
	error (_("Unmatched single quote."));
    }
  ++tokptr;

  value->type = type;
  value->ptr = obstack_base (&tempbuf);
  value->length = obstack_object_size (&tempbuf);

  *outptr = tokptr;

  return quote == '"' ? STRING : CHAR;
}

/* EMBARCADERO LOCAL begin properties */
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
      xfree (tp);
    }
}
/* EMBARCADERO LOCAL end properties */

struct token
{
  char *operator;
  int token;
  enum exp_opcode opcode;
  int cxx_only;
};

static const struct token tokentab3[] =
  {
    {">>=", ASSIGN_MODIFY, BINOP_RSH, 0},
    {"<<=", ASSIGN_MODIFY, BINOP_LSH, 0},
    {"->*", ARROW_STAR, BINOP_END, 1}
  };

static const struct token tokentab2[] =
  {
    {"+=", ASSIGN_MODIFY, BINOP_ADD, 0},
    {"-=", ASSIGN_MODIFY, BINOP_SUB, 0},
    {"*=", ASSIGN_MODIFY, BINOP_MUL, 0},
    {"/=", ASSIGN_MODIFY, BINOP_DIV, 0},
    {"%=", ASSIGN_MODIFY, BINOP_REM, 0},
    {"|=", ASSIGN_MODIFY, BINOP_BITWISE_IOR, 0},
    {"&=", ASSIGN_MODIFY, BINOP_BITWISE_AND, 0},
    {"^=", ASSIGN_MODIFY, BINOP_BITWISE_XOR, 0},
    {"++", INCREMENT, BINOP_END, 0},
    {"--", DECREMENT, BINOP_END, 0},
    {"->", ARROW, BINOP_END, 0},
    {"&&", ANDAND, BINOP_END, 0},
    {"||", OROR, BINOP_END, 0},
    /* "::" is *not* only C++: gdb overrides its meaning in several
       different ways, e.g., 'filename'::func, function::variable.  */
    {"::", COLONCOLON, BINOP_END, 0},
    {"<<", LSH, BINOP_END, 0},
    {">>", RSH, BINOP_END, 0},
    {"==", EQUAL, BINOP_END, 0},
    {"!=", NOTEQUAL, BINOP_END, 0},
    {"<=", LEQ, BINOP_END, 0},
    {">=", GEQ, BINOP_END, 0},
    {".*", DOT_STAR, BINOP_END, 1}
  };

/* Identifier-like tokens.  */
static const struct token ident_tokens[] =
  {
    {"unsigned", UNSIGNED, OP_NULL, 0},
    {"template", TEMPLATE, OP_NULL, 1},
    {"volatile", VOLATILE_KEYWORD, OP_NULL, 0},
    {"struct", STRUCT, OP_NULL, 0},
    {"signed", SIGNED_KEYWORD, OP_NULL, 0},
    {"sizeof", SIZEOF, OP_NULL, 0},
    {"double", DOUBLE_KEYWORD, OP_NULL, 0},
    {"false", FALSEKEYWORD, OP_NULL, 1},
    {"class", CLASS, OP_NULL, 1},
    {"union", UNION, OP_NULL, 0},
    {"short", SHORT, OP_NULL, 0},
    {"const", CONST_KEYWORD, OP_NULL, 0},
    {"enum", ENUM, OP_NULL, 0},
    {"long", LONG, OP_NULL, 0},
    /* EMBARCADERO LOCAL begin MS built-in integer types (__int32, etc) */
    {"__int8", MS_INT8, OP_NULL, 0},
    {"__int16", MS_INT16, OP_NULL, 0},
    {"__int32", MS_INT32, OP_NULL, 0},
    {"__int64", MS_INT64, OP_NULL, 0},
    /* EMBARCADERO LOCAL end MS built-in integer types (__int32, etc) */
    {"true", TRUEKEYWORD, OP_NULL, 1},
    /* EMBARCADERO LOCAL properties */
    {"this", THIS, OP_NULL, 1},
    {"int", INT_KEYWORD, OP_NULL, 0},
    {"new", NEW, OP_NULL, 1},
    {"delete", DELETE, OP_NULL, 1},
    {"operator", OPERATOR, OP_NULL, 1},

    {"and", ANDAND, BINOP_END, 1},
    {"and_eq", ASSIGN_MODIFY, BINOP_BITWISE_AND, 1},
    {"bitand", '&', OP_NULL, 1},
    {"bitor", '|', OP_NULL, 1},
    {"compl", '~', OP_NULL, 1},
    {"not", '!', OP_NULL, 1},
    {"not_eq", NOTEQUAL, BINOP_END, 1},
    {"or", OROR, BINOP_END, 1},
    {"or_eq", ASSIGN_MODIFY, BINOP_BITWISE_IOR, 1},
    {"xor", '^', OP_NULL, 1},
    {"xor_eq", ASSIGN_MODIFY, BINOP_BITWISE_XOR, 1},

    {"const_cast", CONST_CAST, OP_NULL, 1 },
    {"dynamic_cast", DYNAMIC_CAST, OP_NULL, 1 },
    {"static_cast", STATIC_CAST, OP_NULL, 1 },
    {"reinterpret_cast", REINTERPRET_CAST, OP_NULL, 1 }
  };

/* When we find that lexptr (the global var defined in parse.c) is
   pointing at a macro invocation, we expand the invocation, and call
   scan_macro_expansion to save the old lexptr here and point lexptr
   into the expanded text.  When we reach the end of that, we call
   end_macro_expansion to pop back to the value we saved here.  The
   macro expansion code promises to return only fully-expanded text,
   so we don't need to "push" more than one level.

   This is disgusting, of course.  It would be cleaner to do all macro
   expansion beforehand, and then hand that to lexptr.  But we don't
   really know where the expression ends.  Remember, in a command like

     (gdb) break *ADDRESS if CONDITION

   we evaluate ADDRESS in the scope of the current frame, but we
   evaluate CONDITION in the scope of the breakpoint's location.  So
   it's simply wrong to try to macro-expand the whole thing at once.  */
static char *macro_original_text;

/* We save all intermediate macro expansions on this obstack for the
   duration of a single parse.  The expansion text may sometimes have
   to live past the end of the expansion, due to yacc lookahead.
   Rather than try to be clever about saving the data for a single
   token, we simply keep it all and delete it after parsing has
   completed.  */
static struct obstack expansion_obstack;

static void
scan_macro_expansion (char *expansion)
{
  char *copy;

  /* We'd better not be trying to push the stack twice.  */
  gdb_assert (! macro_original_text);

  /* Copy to the obstack, and then free the intermediate
     expansion.  */
  copy = obstack_copy0 (&expansion_obstack, expansion, strlen (expansion));
  xfree (expansion);

  /* Save the old lexptr value, so we can return to it when we're done
     parsing the expanded text.  */
  macro_original_text = lexptr;
  lexptr = copy;
}


static int
scanning_macro_expansion (void)
{
  return macro_original_text != 0;
}


static void 
finished_macro_expansion (void)
{
  /* There'd better be something to pop back to.  */
  gdb_assert (macro_original_text);

  /* Pop back to the original text.  */
  lexptr = macro_original_text;
  macro_original_text = 0;
}


static void
scan_macro_cleanup (void *dummy)
{
  if (macro_original_text)
    finished_macro_expansion ();

  obstack_free (&expansion_obstack, NULL);
}

/* Return true iff the token represents a C++ cast operator.  */

static int
is_cast_operator (const char *token, int len)
{
  return (! strncmp (token, "dynamic_cast", len)
	  || ! strncmp (token, "static_cast", len)
	  || ! strncmp (token, "reinterpret_cast", len)
	  || ! strncmp (token, "const_cast", len));
}

/* The scope used for macro expansion.  */
static struct macro_scope *expression_macro_scope;

/* This is set if a NAME token appeared at the very end of the input
   string, with no whitespace separating the name from the EOF.  This
   is used only when parsing to do field name completion.  */
static int saw_name_at_eof;

/* This is set if the previously-returned token was a structure
   operator -- either '.' or ARROW.  This is used only when parsing to
   do field name completion.  */
static int last_was_structop;

/* Read one token, getting characters through lexptr.  */

static int
lex_one_token (void)
{
  int c;
  int namelen;
  unsigned int i;
  char *tokstart;
  int saw_structop = last_was_structop;
  char *copy;

  last_was_structop = 0;

 retry:

  /* Check if this is a macro invocation that we need to expand.  */
  if (! scanning_macro_expansion ())
    {
      char *expanded = macro_expand_next (&lexptr,
                                          standard_macro_lookup,
                                          expression_macro_scope);

      if (expanded)
        scan_macro_expansion (expanded);
    }

  prev_lexptr = lexptr;

  tokstart = lexptr;
  /* See if it is a special token of length 3.  */
  for (i = 0; i < sizeof tokentab3 / sizeof tokentab3[0]; i++)
    if (strncmp (tokstart, tokentab3[i].operator, 3) == 0)
      {
	if (tokentab3[i].cxx_only
	    && parse_language->la_language != language_cplus)
	  break;

	lexptr += 3;
	yylval.opcode = tokentab3[i].opcode;
	return tokentab3[i].token;
      }

  /* See if it is a special token of length 2.  */
  for (i = 0; i < sizeof tokentab2 / sizeof tokentab2[0]; i++)
    if (strncmp (tokstart, tokentab2[i].operator, 2) == 0)
      {
	if (tokentab2[i].cxx_only
	    && parse_language->la_language != language_cplus)
	  break;

	lexptr += 2;
	yylval.opcode = tokentab2[i].opcode;
	if (in_parse_field && tokentab2[i].token == ARROW)
	  last_was_structop = 1;
	return tokentab2[i].token;
      }

  switch (c = *tokstart)
    {
    case 0:
      /* If we were just scanning the result of a macro expansion,
         then we need to resume scanning the original text.
	 If we're parsing for field name completion, and the previous
	 token allows such completion, return a COMPLETE token.
         Otherwise, we were already scanning the original text, and
         we're really done.  */
      if (scanning_macro_expansion ())
        {
          finished_macro_expansion ();
          goto retry;
        }
      else if (saw_name_at_eof)
	{
	  saw_name_at_eof = 0;
	  return COMPLETE;
	}
      else if (saw_structop)
	return COMPLETE;
      else
        return 0;

    case ' ':
    case '\t':
    case '\n':
      lexptr++;
      goto retry;

    case '[':
    case '(':
      paren_depth++;
      lexptr++;
      return c;

    case ']':
    case ')':
      if (paren_depth == 0)
	return 0;
      paren_depth--;
      lexptr++;
      return c;

    case ',':
      if (comma_terminates
          && paren_depth == 0
          && ! scanning_macro_expansion ())
	return 0;
      lexptr++;
      return c;

    case '.':
      /* Might be a floating point number.  */
      if (lexptr[1] < '0' || lexptr[1] > '9')
	{
	  if (in_parse_field)
	    last_was_structop = 1;
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
	else if (c == '0' && (p[1]=='t' || p[1]=='T' || p[1]=='d' || p[1]=='D'))
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
	toktype = parse_number (tokstart, p - tokstart, got_dot|got_e, &yylval);
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
    case '%':
    case '|':
    case '&':
    case '^':
    case '~':
    case '!':
    case '@':
    case '<':
    case '>':
    case '?':
    case ':':
    case '=':
    case '{':
    case '}':
    symbol:
      lexptr++;
      return c;

    case 'L':
    case 'u':
    case 'U':
      if (tokstart[1] != '"' && tokstart[1] != '\'')
	break;
      /* Fall through.  */
    case '\'':
    case '"':
      {
	int host_len;
	int result = parse_string_or_char (tokstart, &lexptr, &yylval.tsval,
					   &host_len);
	if (result == CHAR)
	  {
	    if (host_len == 0)
	      error (_("Empty character constant."));
	    else if (host_len > 2 && c == '\'')
	      {
		++tokstart;
		namelen = lexptr - tokstart - 1;
		goto tryname;
	      }
	    else if (host_len > 1)
	      error (_("Invalid character constant."));
	  }
	return result;
      }
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
	  if (! is_cast_operator (tokstart, namelen))
	    {
	      /* Scan ahead to get rest of the template specification.  Note
		 that we look ahead only when the '<' adjoins non-whitespace
		 characters; for comparison expressions, e.g. "a < b > c",
		 there must be spaces before the '<', etc. */
               
	      char * p = find_template_name_end (tokstart + namelen);
	      if (p)
		namelen = p - tokstart;
	    }
	  break;
	}
      c = tokstart[++namelen];
    }

  /* The token "if" terminates the expression and is NOT removed from
     the input stream.  It doesn't count if it appears in the
     expansion of a macro.  */
  if (namelen == 2
      && tokstart[0] == 'i'
      && tokstart[1] == 'f'
      && ! scanning_macro_expansion ())
    {
      return 0;
    }

  /* For the same reason (breakpoint conditions), "thread N"
     terminates the expression.  "thread" could be an identifier, but
     an identifier is never followed by a number without intervening
     punctuation.  "task" is similar.  Handle abbreviations of these,
     similarly to breakpoint.c:find_condition_and_thread.  */
  if (namelen >= 1
      && (strncmp (tokstart, "thread", namelen) == 0
	  || strncmp (tokstart, "task", namelen) == 0)
      && (tokstart[namelen] == ' ' || tokstart[namelen] == '\t')
      && ! scanning_macro_expansion ())
    {
      char *p = tokstart + namelen + 1;
      while (*p == ' ' || *p == '\t')
	p++;
      if (*p >= '0' && *p <= '9')
	return 0;
    }

  lexptr += namelen;

  tryname:

  yylval.sval.ptr = tokstart;
  yylval.sval.length = namelen;

  /* Catch specific keywords.  */
  copy = copy_name (yylval.sval);
  for (i = 0; i < sizeof ident_tokens / sizeof ident_tokens[0]; i++)
    if (strcmp (copy, ident_tokens[i].operator) == 0)
      {
	if (ident_tokens[i].cxx_only
	    && parse_language->la_language != language_cplus)
	  break;

	/* It is ok to always set this, even though we don't always
	   strictly need to.  */
	yylval.opcode = ident_tokens[i].opcode;
	return ident_tokens[i].token;
      }

  if (*tokstart == '$')
    return VARIABLE;

  if (in_parse_field && *lexptr == '\0')
    saw_name_at_eof = 1;
  return NAME;
}

/* An object of this type is pushed on a FIFO by the "outer" lexer.  */
typedef struct
{
  int token;
  YYSTYPE value;
} token_and_value;

DEF_VEC_O (token_and_value);

/* A FIFO of tokens that have been read but not yet returned to the
   parser.  */
static VEC (token_and_value) *token_fifo;

/* Non-zero if the lexer should return tokens from the FIFO.  */
static int popping;

/* Temporary storage for c_lex; this holds symbol names as they are
   built up.  */
static struct obstack name_obstack;

/* Classify a NAME token.  The contents of the token are in `yylval'.
   Updates yylval and returns the new token type.  BLOCK is the block
   in which lookups start; this can be NULL to mean the global
   scope.  */
static int
classify_name (struct block *block)
{
  struct symbol *sym;
  char *copy;
  int is_a_field_of_this = 0;

  copy = copy_name (yylval.sval);

  sym = lookup_symbol (copy, block, VAR_DOMAIN, 
		       parse_language->la_language == language_cplus
		       ? &is_a_field_of_this : (int *) NULL);

  if (sym && SYMBOL_CLASS (sym) == LOC_BLOCK)
    {
      yylval.ssym.sym = sym;
      yylval.ssym.is_a_field_of_this = is_a_field_of_this;
      return BLOCKNAME;
    }
  else if (!sym)
    {
      /* See if it's a file name. */
      struct symtab *symtab;

      symtab = lookup_symtab (copy);
      if (symtab)
	{
	  yylval.bval = BLOCKVECTOR_BLOCK (BLOCKVECTOR (symtab), STATIC_BLOCK);
	  return FILENAME;
	}
    }

  if (sym && SYMBOL_CLASS (sym) == LOC_TYPEDEF)
    {
      yylval.tsym.type = SYMBOL_TYPE (sym);
      return TYPENAME;
    }

  yylval.tsym.type
    = language_lookup_primitive_type_by_name (parse_language,
					      parse_gdbarch, copy);
  if (yylval.tsym.type != NULL)
    return TYPENAME;

  /* Input names that aren't symbols but ARE valid hex numbers, when
     the input radix permits them, can be names or numbers depending
     on the parse.  Note we support radixes > 16 here.  */
  if (!sym
      && ((copy[0] >= 'a' && copy[0] < 'a' + input_radix - 10)
	  || (copy[0] >= 'A' && copy[0] < 'A' + input_radix - 10)))
    {
      YYSTYPE newlval;	/* Its value is ignored.  */
      int hextype = parse_number (copy, yylval.sval.length, 0, &newlval);
      if (hextype == INT)
	{
	  yylval.ssym.sym = sym;
	  yylval.ssym.is_a_field_of_this = is_a_field_of_this;
	  return NAME_OR_INT;
	}
    }

  /* Any other kind of symbol */
  yylval.ssym.sym = sym;
  yylval.ssym.is_a_field_of_this = is_a_field_of_this;

  if (sym == NULL
      && parse_language->la_language == language_cplus
      && !is_a_field_of_this
      && !lookup_minimal_symbol (copy, NULL, NULL))
    return UNKNOWN_CPP_NAME;

  return NAME;
}

/* Like classify_name, but used by the inner loop of the lexer, when a
   name might have already been seen.  FIRST_NAME is true if the token
   in `yylval' is the first component of a name, false otherwise.  If
   this function returns NAME, it might not have updated `yylval'.
   This is ok because the caller only cares about TYPENAME.  */
static int
classify_inner_name (struct block *block, int first_name)
{
  struct type *type, *new_type;
  char *copy;

  if (first_name)
    return classify_name (block);

  type = check_typedef (yylval.tsym.type);
  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
      && TYPE_CODE (type) != TYPE_CODE_UNION
      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
    /* We know the caller won't expect us to update yylval.  */
    return NAME;

  copy = copy_name (yylval.tsym.stoken);
  new_type = cp_lookup_nested_type (type, copy, block);

  if (new_type == NULL)
    /* We know the caller won't expect us to update yylval.  */
    return NAME;

  yylval.tsym.type = new_type;
  return TYPENAME;
}

/* The outer level of a two-level lexer.  This calls the inner lexer
   to return tokens.  It then either returns these tokens, or
   aggregates them into a larger token.  This lets us work around a
   problem in our parsing approach, where the parser could not
   distinguish between qualified names and qualified types at the
   right point.
   
   This approach is still not ideal, because it mishandles template
   types.  See the comment in lex_one_token for an example.  However,
   this is still an improvement over the earlier approach, and will
   suffice until we move to better parsing technology.  */
static int
yylex (void)
{
  token_and_value current;
  int first_was_coloncolon, last_was_coloncolon, first_iter;

  if (popping && !VEC_empty (token_and_value, token_fifo))
    {
      token_and_value tv = *VEC_index (token_and_value, token_fifo, 0);
      VEC_ordered_remove (token_and_value, token_fifo, 0);
      yylval = tv.value;
      return tv.token;
    }
  popping = 0;

  current.token = lex_one_token ();
  if (current.token == NAME)
    current.token = classify_name (expression_context_block);
  if (parse_language->la_language != language_cplus
      || (current.token != TYPENAME && current.token != COLONCOLON))
    return current.token;

  first_was_coloncolon = current.token == COLONCOLON;
  last_was_coloncolon = first_was_coloncolon;
  obstack_free (&name_obstack, obstack_base (&name_obstack));
  if (!last_was_coloncolon)
    obstack_grow (&name_obstack, yylval.sval.ptr, yylval.sval.length);
  current.value = yylval;
  first_iter = 1;
  while (1)
    {
      token_and_value next;

      next.token = lex_one_token ();
      next.value = yylval;

      if (next.token == NAME && last_was_coloncolon)
	{
	  int classification;

	  classification = classify_inner_name (first_was_coloncolon
						? NULL
						: expression_context_block,
						first_iter);
	  /* We keep going until we either run out of names, or until
	     we have a qualified name which is not a type.  */
	  if (classification != TYPENAME)
	    {
	      /* Push the final component and leave the loop.  */
	      VEC_safe_push (token_and_value, token_fifo, &next);
	      break;
	    }

	  /* Update the partial name we are constructing.  */
	  if (!first_iter)
	    {
	      /* We don't want to put a leading "::" into the name.  */
	      obstack_grow_str (&name_obstack, "::");
	    }
	  obstack_grow (&name_obstack, next.value.sval.ptr,
			next.value.sval.length);

	  yylval.sval.ptr = obstack_base (&name_obstack);
	  yylval.sval.length = obstack_object_size (&name_obstack);
	  current.value = yylval;
	  current.token = classification;

	  last_was_coloncolon = 0;
	}
      else if (next.token == COLONCOLON && !last_was_coloncolon)
	last_was_coloncolon = 1;
      else
	{
	  /* We've reached the end of the name.  */
	  VEC_safe_push (token_and_value, token_fifo, &next);
	  break;
	}

      first_iter = 0;
    }

  popping = 1;

  /* If we ended with a "::", insert it too.  */
  if (last_was_coloncolon)
    {
      token_and_value cc;
      memset (&cc, 0, sizeof (token_and_value));
      if (first_was_coloncolon && first_iter)
	{
	  yylval = cc.value;
	  return COLONCOLON;
	}
      cc.token = COLONCOLON;
      VEC_safe_insert (token_and_value, token_fifo, 0, &cc);
    }

  yylval = current.value;
  yylval.sval.ptr = obstack_copy0 (&expansion_obstack,
				   yylval.sval.ptr,
				   yylval.sval.length);
  return current.token;
}

int
c_parse (void)
{
  int result;
  struct cleanup *back_to = make_cleanup (free_current_contents,
					  &expression_macro_scope);

  /* Set up the scope for macro expansion.  */
  expression_macro_scope = NULL;

  if (expression_context_block)
    expression_macro_scope
      = sal_macro_scope (find_pc_line (expression_context_pc, 0));
  else
    expression_macro_scope = default_macro_scope ();
  if (! expression_macro_scope)
    expression_macro_scope = user_macro_scope ();

  /* Initialize macro expansion code.  */
  obstack_init (&expansion_obstack);
  gdb_assert (! macro_original_text);
  make_cleanup (scan_macro_cleanup, 0);

  make_cleanup_restore_integer (&yydebug);
  yydebug = parser_debug;

  /* Initialize some state used by the lexer.  */
  last_was_structop = 0;
  saw_name_at_eof = 0;

  VEC_free (token_and_value, token_fifo);
  popping = 0;
  obstack_init (&name_obstack);
  make_cleanup_obstack_free (&name_obstack);

  result = yyparse ();
  do_cleanups (back_to);
  return result;
}


void
yyerror (char *msg)
{
  if (prev_lexptr)
    lexptr = prev_lexptr;

  error (_("A %s in expression, near `%s'."), (msg ? msg : "error"), lexptr);
}
