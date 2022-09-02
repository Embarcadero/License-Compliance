/* YACC parser for C expressions, for GDB.
   Copyright 1986, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997,
   1998, 1999, 2000, 2003, 2004
   Free Software Foundation, Inc.

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
/* APPLE LOCAL ObjC */
#include "objc-lang.h" /* For ObjC language constructs. */

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

/* APPLE LOCAL - Avoid calling lookup_objc_class unnecessarily.  */
static int square_bracket_seen = 0;

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
    /* APPLE LOCAL ObjC */
    struct objc_class_str class;

    struct stoken_vector svec;
    struct type **tvec;
    int *ivec;
  }

%{
/* YYSTYPE gets defined by %union */
static int parse_number (char *, int, int, YYSTYPE *);

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
%type <tval> type typebase qualified_type
%type <tvec> nonempty_typelist
/* %type <bval> block */

/* Fancy type parsing.  */
%type <voidval> func_mod direct_abs_decl abs_decl
%type <tval> ptype
%type <lval> array_mod

%token <typed_val_int> INT
%token <typed_val_float> FLOAT

/* Both NAME and TYPENAME tokens represent symbols in the input,
   and both convey their data as strings.
   But a TYPENAME is a string that happens to be defined as a typedef
   or builtin type name (such as int or char)
   and a NAME is any other symbol.
   Contexts where this distinction is not important can use the
   nonterminal "name", which matches either NAME or TYPENAME.  */

%token <tsval> STRING
%token <tsval> CHAR
/* APPLE LOCAL begin ObjC */
%token <sval> OBJC_NSSTRING /* ObjC Foundation "NSString" literal */ 
%token <sval> OBJC_SELECTOR /* ObjC "@selector" pseudo-operator   */ 
%token <class> OBJC_CLASSNAME /* ObjC Class name */ 
/* APPLE LOCAL end ObjC */
%token <ssym> NAME /* BLOCKNAME defined below to give it higher precedence. */
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

%token STRUCT CLASS UNION ENUM SIZEOF UNSIGNED COLONCOLON
%token TEMPLATE
%token ERROR

/* Special type cases, put in to allow the parser to distinguish different
   legal basetypes.  */
%token SIGNED_KEYWORD LONG SHORT INT_KEYWORD CONST_KEYWORD VOLATILE_KEYWORD DOUBLE_KEYWORD
/* EMBARCADERO LOCAL MS built-in integer types (__int32, etc) */
%token MS_INT8 MS_INT16 MS_INT32 MS_INT64

%token <voidval> VARIABLE

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
%right ARROW '.' '[' '('
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

exp	:	exp ARROW '*' exp
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

exp	:	exp '.' '*' exp
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

/* APPLE LOCAL begin ObjC */
/* The rules below parse ObjC message calls of the form:
   '[' target selector {':' argument}* ']' */

exp	: 	'[' TYPENAME
			{
			  CORE_ADDR class;

			  class = lookup_objc_class (copy_name ($2.stoken));
			  if (class == 0)
			    error ("%s is not an ObjC Class", 
				   copy_name ($2.stoken));
			  write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (builtin_type_void_data_ptr);
			  write_exp_elt_longcst ((LONGEST) class);
			  write_exp_elt_opcode (OP_LONG);
			  start_msglist();
			}
		msglist ']'
			{ write_exp_elt_opcode (OP_OBJC_MSGCALL);
			  end_msglist();
			  write_exp_elt_opcode (OP_OBJC_MSGCALL); 
			}
	;

exp	:	'[' OBJC_CLASSNAME
			{
			  write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (builtin_type_void_data_ptr);
			  write_exp_elt_longcst ((LONGEST) $2.class);
			  write_exp_elt_opcode (OP_LONG);
			  start_msglist();
			}
		msglist ']'
			{ write_exp_elt_opcode (OP_OBJC_MSGCALL);
			  end_msglist();
			  write_exp_elt_opcode (OP_OBJC_MSGCALL); 
			}
	;

exp	:	'[' exp
			{ start_msglist(); }
		msglist ']'
			{ write_exp_elt_opcode (OP_OBJC_MSGCALL);
			  end_msglist();
			  write_exp_elt_opcode (OP_OBJC_MSGCALL); 
			}
	;

msglist :	name
			{ add_msglist(&$1, 0); }
	|	msgarglist
	;

msgarglist :	msgarg
	|	msgarglist msgarg
	;

msgarg	:	name ':' exp
			{ add_msglist(&$1, 1); }
	|	':' exp	/* Unnamed argument. */
			{ add_msglist(0, 1);   }
	|	',' exp	/* Variable number of arguments. */
			{ add_msglist(0, 0);   }
	;
/* APPLE LOCAL end ObjC */
 
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

exp	:	variable
	;

exp	:	VARIABLE
			/* Already written by write_dollar_variable. */
	;

/* APPLE LOCAL begin ObjC */
exp	:	OBJC_SELECTOR 
			{
			  write_exp_elt_opcode (OP_OBJC_SELECTOR);
			  write_exp_string ($1);
			  write_exp_elt_opcode (OP_OBJC_SELECTOR); }
	;
/* APPLE LOCAL end ObjC */

exp	:	SIZEOF '(' type ')'	%prec UNARY
			{ write_exp_elt_opcode (OP_LONG);
			  write_exp_elt_type (builtin_type (current_gdbarch)->builtin_int);
			  CHECK_TYPEDEF ($3);
			  write_exp_elt_longcst ((LONGEST) TYPE_LENGTH ($3));
			  write_exp_elt_opcode (OP_LONG); }
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
				    error ("Undefined string concatenation.");
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

exp     :	OBJC_NSSTRING	/* ObjC NextStep NSString constant
				 * of the form '@' '"' string '"'.
				 */
			{ write_exp_elt_opcode (OP_OBJC_NSSTRING);
			  write_exp_string ($1);
			  write_exp_elt_opcode (OP_OBJC_NSSTRING); }
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
                          write_exp_elt_type (builtin_type (current_gdbarch)->builtin_bool);
                          write_exp_elt_longcst ((LONGEST) 1);
                          write_exp_elt_opcode (OP_LONG); }
	;

exp     :       FALSEKEYWORD   
                        { write_exp_elt_opcode (OP_LONG);
                          write_exp_elt_type (builtin_type (current_gdbarch)->builtin_bool);
                          write_exp_elt_longcst ((LONGEST) 0);
                          write_exp_elt_opcode (OP_LONG); }
	;

/* end of C++.  */

block	:	BLOCKNAME
			{
			  if ($1.sym)
			    $$ = SYMBOL_BLOCK_VALUE ($1.sym);
			  else
			    error ("No file or function \"%s\".",
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
					     VAR_DOMAIN, (int *) NULL,
					     (struct symtab **) NULL);
			  if (!tem || SYMBOL_CLASS (tem) != LOC_BLOCK)
			    error ("No function \"%s\" in specified context.",
				   copy_name ($3));
			  $$ = SYMBOL_BLOCK_VALUE (tem); }
	;

variable:	block COLONCOLON name
			{ struct symbol *sym;
			  sym = lookup_symbol (copy_name ($3), $1,
					       VAR_DOMAIN, (int *) NULL,
					       (struct symtab **) NULL);
			  if (sym == 0)
			    error ("No symbol \"%s\" in specified context.",
				   copy_name ($3));

			  write_exp_elt_opcode (OP_VAR_VALUE);
			  /* block_found is set by lookup_symbol.  */
			  write_exp_elt_block (block_found);
			  write_exp_elt_sym (sym);
			  write_exp_elt_opcode (OP_VAR_VALUE); }
	;

qualified_name:	typebase COLONCOLON name
			{
			  struct type *type = $1;
			  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
			      && TYPE_CODE (type) != TYPE_CODE_UNION
			      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
			    error ("`%s' is not defined as an aggregate type.",
				   TYPE_NAME (type));

			  write_exp_elt_opcode (OP_SCOPE);
			  write_exp_elt_type (type);
			  write_exp_string ($3);
			  write_exp_elt_opcode (OP_SCOPE);
			}
	|	typebase COLONCOLON '~' name
			{
			  struct type *type = $1;
			  struct stoken tmp_token;
			  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
			      && TYPE_CODE (type) != TYPE_CODE_UNION
			      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
			    error ("`%s' is not defined as an aggregate type.",
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
	;

variable:	qualified_name
	|	COLONCOLON name
			{
			  char *name = copy_name ($2);
			  struct symbol *sym;
			  struct minimal_symbol *msymbol;

			  sym =
			    lookup_symbol (name, (const struct block *) NULL,
					   VAR_DOMAIN, (int *) NULL,
					   (struct symtab **) NULL);
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
			    {
			      write_exp_msymbol (msymbol,
						 lookup_function_type (builtin_type (current_gdbarch)->builtin_int),
						 builtin_type (current_gdbarch)->builtin_int);
			    }
			  else
			    if (!have_full_symbols () && !have_partial_symbols ())
			      error ("No symbol table is loaded.  Use the \"file\" command.");
			    else
			      error ("No symbol \"%s\" in current context.", name);
			}
	;

variable:	name_not_typename
			{ struct symbol *sym = $1.sym;

			  if (sym)
			    {
			      if (symbol_read_needs_frame (sym))
				{
				  if (innermost_block == 0 ||
				      contained_in (block_found, 
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
			      /* C++/ObjC: it hangs off of `this'.  Must
			         not inadvertently convert from a method call
				 to data ref.  */
			      if (innermost_block == 0 || 
				  contained_in (block_found, innermost_block))
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
						       0,
						       (struct symtab **) NULL);
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
				  if (current_language->la_language == language_cplus)
				    {
				      write_exp_elt_opcode (OP_THIS);
				      write_exp_elt_opcode (OP_THIS);
				    }
				  else if (current_language->la_language == language_objc
					  || current_language->la_language == language_objcplus)
				    {
				      write_exp_elt_opcode (OP_OBJC_SELF);
				      write_exp_elt_opcode (OP_OBJC_SELF);
				    }
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
				{
				  write_exp_msymbol (msymbol,
						     lookup_function_type (builtin_type (current_gdbarch)->builtin_int),
						     builtin_type (current_gdbarch)->builtin_int);
				}
			      else if (!have_full_symbols () && !have_partial_symbols ())
				error ("No symbol table is loaded.  Use the \"file\" command.");
			      else
				error ("No symbol \"%s\" in current context.",
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
	:	TYPENAME
			{ $$ = $1.type; }
	|	OBJC_CLASSNAME
			{
			  if ($1.type == NULL)
			    error ("No symbol \"%s\" in current context.", 
				   copy_name($1.stoken));
			  else
			    $$ = $1.type;
			}
	|	INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_int; }
	|	LONG
			{ $$ = builtin_type (current_gdbarch)->builtin_long; }
	|	SHORT
			{ $$ = builtin_type (current_gdbarch)->builtin_short; }
	|	LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long; }
	|	LONG SIGNED_KEYWORD INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long; }
	|	LONG SIGNED_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long; }
	|	SIGNED_KEYWORD LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long; }
	|	UNSIGNED LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long; }
	|	LONG UNSIGNED INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long; }
	|	LONG UNSIGNED
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long; }
	|	LONG LONG
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	LONG LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	LONG LONG SIGNED_KEYWORD INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	LONG LONG SIGNED_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	SIGNED_KEYWORD LONG LONG
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	SIGNED_KEYWORD LONG LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long_long; }
	|	UNSIGNED LONG LONG
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long_long; }
	|	UNSIGNED LONG LONG INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long_long; }
	|	LONG LONG UNSIGNED
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long_long; }
	|	LONG LONG UNSIGNED INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_long_long; }
	|	SHORT INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_short; }
	|	SHORT SIGNED_KEYWORD INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_short; }
	|	SHORT SIGNED_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_short; }
	|	UNSIGNED SHORT INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_short; }
	|	SHORT UNSIGNED 
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_short; }
	|	SHORT UNSIGNED INT_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_short; }
	|	DOUBLE_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_double; }
	|	LONG DOUBLE_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_long_double; }
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
			{ $$ = lookup_unsigned_typename (TYPE_NAME($2.type)); }
	|	UNSIGNED
			{ $$ = builtin_type (current_gdbarch)->builtin_unsigned_int; }
	|	SIGNED_KEYWORD typename
			{ $$ = lookup_signed_typename (TYPE_NAME($2.type)); }
	|	SIGNED_KEYWORD
			{ $$ = builtin_type (current_gdbarch)->builtin_int; }
		/* EMBARCADERO LOCAL begin MS built-in integer types (__int32, etc) */
	|	MS_INT8
			{ $$ = builtin_type_signed_char; }
	|	MS_INT16
			{ $$ = builtin_type_short; }
	|	MS_INT32
			{ $$ = builtin_type_int; }
	|	MS_INT64
			{ $$ = builtin_type_long_long; }
	|	UNSIGNED MS_INT8
			{ $$ = builtin_type_unsigned_char; }
	|	UNSIGNED MS_INT16
			{ $$ = builtin_type_unsigned_short; }
	|	UNSIGNED MS_INT32
			{ $$ = builtin_type_unsigned_int; }
	|	UNSIGNED MS_INT64
			{ $$ = builtin_type_unsigned_long_long; }
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
	| qualified_type
	;

/* FIXME: carlton/2003-09-25: This next bit leads to lots of
   reduce-reduce conflicts, because the parser doesn't know whether or
   not to use qualified_name or qualified_type: the rules are
   identical.  If the parser is parsing 'A::B::x', then, when it sees
   the second '::', it knows that the expression to the left of it has
   to be a type, so it uses qualified_type.  But if it is parsing just
   'A::B', then it doesn't have any way of knowing which rule to use,
   so there's a reduce-reduce conflict; it picks qualified_name, since
   that occurs earlier in this file than qualified_type.

   There's no good way to fix this with the grammar as it stands; as
   far as I can tell, some of the problems arise from ambiguities that
   GDB introduces ('start' can be either an expression or a type), but
   some of it is inherent to the nature of C++ (you want to treat the
   input "(FOO)" fairly differently depending on whether FOO is an
   expression or a type, and if FOO is a complex expression, this can
   be hard to determine at the right time).  Fortunately, it works
   pretty well in most cases.  For example, if you do 'ptype A::B',
   where A::B is a nested type, then the parser will mistakenly
   misidentify it as an expression; but evaluate_subexp will get
   called with 'noside' set to EVAL_AVOID_SIDE_EFFECTS, and everything
   will work out anyways.  But there are situations where the parser
   will get confused: the most common one that I've run into is when
   you want to do

     print *((A::B *) x)"

   where the parser doesn't realize that A::B has to be a type until
   it hits the first right paren, at which point it's too late.  (The
   workaround is to type "print *(('A::B' *) x)" instead.)  (And
   another solution is to fix our symbol-handling code so that the
   user never wants to type something like that in the first place,
   because we get all the types right without the user's help!)

   Perhaps we could fix this by making the lexer smarter.  Some of
   this functionality used to be in the lexer, but in a way that
   worked even less well than the current solution: that attempt
   involved having the parser sometimes handle '::' and having the
   lexer sometimes handle it, and without a clear division of
   responsibility, it quickly degenerated into a big mess.  Probably
   the eventual correct solution will give more of a role to the lexer
   (ideally via code that is shared between the lexer and
   decode_line_1), but I'm not holding my breath waiting for somebody
   to get around to cleaning this up...  */

qualified_type: typebase COLONCOLON name
		{
		  struct type *type = $1;
		  struct type *new_type;
		  char *ncopy = alloca ($3.length + 1);

		  memcpy (ncopy, $3.ptr, $3.length);
		  ncopy[$3.length] = '\0';

		  if (TYPE_CODE (type) != TYPE_CODE_STRUCT
		      && TYPE_CODE (type) != TYPE_CODE_UNION
		      && TYPE_CODE (type) != TYPE_CODE_NAMESPACE)
		    error ("`%s' is not defined as an aggregate type.",
			   TYPE_NAME (type));

		  new_type = cp_lookup_nested_type (type, ncopy,
						    expression_context_block);
		  if (new_type == NULL)
		    error ("No type \"%s\" within class or namespace \"%s\".",
			   ncopy, TYPE_NAME (type));
		  
		  $$ = new_type;
		}
	;

typename:	TYPENAME
	|	INT_KEYWORD
		{
		  $$.stoken.ptr = "int";
		  $$.stoken.length = 3;
		  $$.type = builtin_type (current_gdbarch)->builtin_int;
		}
	|	LONG
		{
		  $$.stoken.ptr = "long";
		  $$.stoken.length = 4;
		  $$.type = builtin_type (current_gdbarch)->builtin_long;
		}
	|	SHORT
		{
		  $$.stoken.ptr = "short";
		  $$.stoken.length = 5;
		  $$.type = builtin_type (current_gdbarch)->builtin_short;
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

name	:	NAME { $$ = $1.stoken; }
	|	BLOCKNAME { $$ = $1.stoken; }
	|	TYPENAME { $$ = $1.stoken; }
	|	OBJC_CLASSNAME { $$ = $1.stoken; }
	|	NAME_OR_INT  { $$ = $1.stoken; }
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
	;

%%

/* Take care of parsing a number (anything that starts with a digit).
   Set yylval and return the token type; update lexptr.
   LEN is the number of characters in it.  */

/*** Needs some error checking for the float case ***/

static int
parse_number (p, len, parsed_float, putithere)
     char *p;
     int len;
     int parsed_float;
     YYSTYPE *putithere;
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
      /* It's a float since it contains a point or an exponent.  */
      char c;
      int num = 0;	/* number of tokens scanned by scanf */
      char saved_char = p[len];

      p[len] = 0;	/* null-terminate the token */
      if (sizeof (putithere->typed_val_float.dval) <= sizeof (float))
	num = sscanf (p, "%g%c", (float *) &putithere->typed_val_float.dval,&c);
      else if (sizeof (putithere->typed_val_float.dval) <= sizeof (double))
	num = sscanf (p, "%lg%c", (double *) &putithere->typed_val_float.dval,&c);
      else
	{
#ifdef SCANF_HAS_LONG_DOUBLE
	  num = sscanf (p, "%Lg%c", &putithere->typed_val_float.dval,&c);
#else
	  /* Scan it into a double, then assign it to the long double.
	     This at least wins with values representable in the range
	     of doubles. */
	  double temp;
	  num = sscanf (p, "%lg%c", &temp,&c);
	  putithere->typed_val_float.dval = temp;
#endif
	}
      p[len] = saved_char;	/* restore the input stream */
      if (num == 1) 		/* check scanf found ONLY a float ... */
        putithere->typed_val_float.type =
          builtin_type (current_gdbarch)->builtin_double;
      else if (num == 2)
	{
	  /* There's no way to tell, using sscanf, whether we actually
	     did ingest all the input.  But this check will catch things
	     like: 123fghi.jklmn, though of course it will be fooled by
	     123fghi.jklmf.  I'm not really all that worried about this,
	     however.  */

	  if (c != p[len-1])
	    return ERROR;

	  /* See if it has `f' or `l' suffix (float or long double).  */
	  
	  c = tolower (c);

	  if (c == 'f')
	    putithere->typed_val_float.type = builtin_type (current_gdbarch)->builtin_float;
	  else if (c == 'l')
	    putithere->typed_val_float.type = builtin_type (current_gdbarch)->builtin_long_double;
	  else
	    return ERROR;
	}
      else
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
	unsigned_p = 1;     /* Try something unsigned */
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
     (which always produces a zero result).  Sometimes TARGET_INT_BIT
     or TARGET_LONG_BIT will be that big, sometimes not.  To deal with
     the case where it is we just always shift the value more than
     once, with fewer bits each time.  */

  un = (ULONGEST)n >> 2;
  if (long_p == 0
      && (un >> (TARGET_INT_BIT - 2)) == 0)
    {
      high_bit = ((ULONGEST)1) << (TARGET_INT_BIT-1);

      /* A large decimal (not hex or octal) constant (between INT_MAX
	 and UINT_MAX) is a long or unsigned long, according to ANSI,
	 never an unsigned int, but this code treats it as unsigned
	 int.  This probably should be fixed.  GCC gives a warning on
	 such constants.  */

      unsigned_type = builtin_type (current_gdbarch)->builtin_unsigned_int;
      signed_type = builtin_type (current_gdbarch)->builtin_int;
    }
  else if (long_p <= 1
	   && (un >> (TARGET_LONG_BIT - 2)) == 0)
    {
      high_bit = ((ULONGEST)1) << (TARGET_LONG_BIT-1);
      unsigned_type = builtin_type (current_gdbarch)->builtin_unsigned_long;
      signed_type = builtin_type (current_gdbarch)->builtin_long;
    }
  else
    {
      int shift;
      if (sizeof (ULONGEST) * HOST_CHAR_BIT < TARGET_LONG_LONG_BIT)
	/* A long long does not fit in a LONGEST.  */
	shift = (sizeof (ULONGEST) * HOST_CHAR_BIT - 1);
      else
	shift = (TARGET_LONG_LONG_BIT - 1);
      high_bit = (ULONGEST) 1 << shift;
      unsigned_type = builtin_type (current_gdbarch)->builtin_unsigned_long_long;
      signed_type = builtin_type (current_gdbarch)->builtin_long_long;
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
	error ("Unterminated string in expression.");
      else
	error ("Unmatched single quote.");
    }
  ++tokptr;

  value->type = type;
  value->ptr = obstack_base (&tempbuf);
  value->length = obstack_object_size (&tempbuf);

  *outptr = tokptr;

  return quote == '"' ? STRING : CHAR;
}

struct token
{
  char *operator;
  int token;
  enum exp_opcode opcode;
};

static const struct token tokentab3[] =
  {
    {">>=", ASSIGN_MODIFY, BINOP_RSH},
    {"<<=", ASSIGN_MODIFY, BINOP_LSH}
  };

static const struct token tokentab2[] =
  {
    {"+=", ASSIGN_MODIFY, BINOP_ADD},
    {"-=", ASSIGN_MODIFY, BINOP_SUB},
    {"*=", ASSIGN_MODIFY, BINOP_MUL},
    {"/=", ASSIGN_MODIFY, BINOP_DIV},
    {"%=", ASSIGN_MODIFY, BINOP_REM},
    {"|=", ASSIGN_MODIFY, BINOP_BITWISE_IOR},
    {"&=", ASSIGN_MODIFY, BINOP_BITWISE_AND},
    {"^=", ASSIGN_MODIFY, BINOP_BITWISE_XOR},
    {"++", INCREMENT, BINOP_END},
    {"--", DECREMENT, BINOP_END},
    {"->", ARROW, BINOP_END},
    {"&&", ANDAND, BINOP_END},
    {"||", OROR, BINOP_END},
    {"::", COLONCOLON, BINOP_END},
    {"<<", LSH, BINOP_END},
    {">>", RSH, BINOP_END},
    {"==", EQUAL, BINOP_END},
    {"!=", NOTEQUAL, BINOP_END},
    {"<=", LEQ, BINOP_END},
    {">=", GEQ, BINOP_END}
  };

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
yylex ()
{
  int c;
  int tokchar;
  int namelen;
  unsigned int i;
  char *tokstart;
  struct symbol * sym_class = NULL;
  int saw_structop = last_was_structop;
  int unquoted_expr;

  last_was_structop = 0;
   
 retry:

  /* Check if this is a macro invocation that we need to expand.  */
  if (! scanning_macro_expansion ())
    {
      char *expanded = macro_expand_next (&lexptr,
                                          expression_macro_lookup_func,
                                          expression_macro_lookup_baton);

      if (expanded)
        scan_macro_expansion (expanded);
    }

  prev_lexptr = lexptr;
  unquoted_expr = 1;

  tokstart = lexptr;
  /* See if it is a special token of length 3.  */
  for (i = 0; i < sizeof tokentab3 / sizeof tokentab3[0]; i++)
    if (strncmp (tokstart, tokentab3[i].operator, 3) == 0)
      {
	lexptr += 3;
	yylval.opcode = tokentab3[i].opcode;
	return tokentab3[i].token;
      }

  /* See if it is a special token of length 2.  */
  for (i = 0; i < sizeof tokentab2 / sizeof tokentab2[0]; i++)
    if (strncmp (tokstart, tokentab2[i].operator, 2) == 0)
      {
	lexptr += 2;
	yylval.opcode = tokentab2[i].opcode;
	if (in_parse_field && tokentab2[i].opcode == ARROW)
	  last_was_structop = 1;
	return tokentab2[i].token;
      }

  switch (tokchar = c = *tokstart)
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
      if (comma_terminates
          && paren_depth == 0
          && ! scanning_macro_expansion ())
	return 0;
      lexptr++;
      return c;

    case '.':
      if ((input_radix != 16 && !isdigit (lexptr[1]))
	/* Might be a floating point num in P format,
	   e.g. 0x1.e84810f5c28fp+19 */
	|| (input_radix == 16 && !ishexnumber (lexptr[1])))
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
	int got_dot = 0, got_e = 0, got_p = 0, toktype;
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
            /* APPLE LOCAL: Recognize the P formatting of floating point 
               numbers with two hex components, e.g. 
                  1000000.53 == 0x1.e84810f5c28f60000p+19 */
            else if (got_dot && hex && (*p == 'p' || *p == 'P'))
              got_p = 1;
	    else if (((got_e && (p[-1] == 'e' || p[-1] == 'E')) ||
	              (got_p && (p[-1] == 'p' || p[-1] == 'P')))
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
	toktype = parse_number (tokstart, p - tokstart, got_dot|got_e|got_p, 
                                &yylval);
        if (toktype == ERROR)
	  {
	    char *err_copy = (char *) alloca (p - tokstart + 1);

	    memcpy (err_copy, tokstart, p - tokstart);
	    err_copy[p - tokstart] = 0;
	    error ("Invalid number \"%s\".", err_copy);
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
    case '<':
    case '>':
      /* APPLE LOCAL begin avoid calling lookup_objc_class unnecessarily.  */
      /* case '[':  moved down below */
      /* case ']':  moved down below */
      /* APPLE LOCAL end avoid calling lookup_objc_class unnecessarily.  */
    case '?':
    case ':':
    case '=':
    case '{':
    case '}':
    symbol:
      lexptr++;
      return c;

    /* APPLE LOCAL begin avoid calling lookup_objc_class unnecessarily.  */
    case '[':
      square_bracket_seen = 1;
      lexptr++;
      return c;

    case ']':
      square_bracket_seen = 0;
      lexptr++;
      return c;

    /* APPLE LOCAL end  avoid calling lookup_objc_class unnecessarily.  */
    case '@':
      if (strncmp (tokstart, "@selector", 9) == 0)
	{
	  /* EMBARCADERO LOCAL begin trunk merge for wide char support */
	  char *tokptr;
	  int tempbufindex;
	  static char *tempbuf = 0;
	  static int tempbufsize;
	  /* EMBARCADERO LOCAL end trunk merge for wide char support */
	  tokptr = strchr (tokstart, '(');
	  if (tokptr == NULL)
	    error ("Missing '(' in @selector(...)");
	  tempbufindex = 0;
	  /* skip the '(' */
	  tokptr++;
	  do {
	    /* Grow the static temp buffer if necessary, including allocating
	       the first one on demand. */
	    if (tempbufindex + 1 >= tempbufsize)
	      {
		tempbuf = (char *) realloc (tempbuf, tempbufsize += 64);
	      }
	    tempbuf[tempbufindex++] = *tokptr++;
	  } while ((*tokptr != ')') && (*tokptr != '\0'));
	  if (*tokptr++ != ')')
	    error ("Missing ')' in @selector(...)");
	  tempbuf[tempbufindex] = '\0';
	  yylval.sval.ptr = tempbuf;
	  yylval.sval.length = tempbufindex;
	  lexptr = tokptr;
	  return OBJC_SELECTOR;
	}
      if (tokstart[1] != '"')
        {
          lexptr++;
          return c;
        }
      /* ObjC NSString constant: fall through and parse like STRING. */
      tokstart++;

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
	      error ("Empty character constant.");
	    else if (host_len > 2 && c == '\'')
	      {
		++tokstart;
		namelen = lexptr - tokstart - 1;
		goto tryname;
	      }
	    else if (host_len > 1)
	      error ("Invalid character constant.");
	  }
	return result;
      }
    }

  if (!(c == '_' || c == '$'
	|| (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')))
    /* We must have come across a bad character (e.g. ';').  */
    error ("Invalid character '%c' in expression.", c);

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
               /* Scan ahead to get rest of the template specification.  Note
                  that we look ahead only when the '<' adjoins non-whitespace
                  characters; for comparison expressions, e.g. "a < b > c",
                  there must be spaces before the '<', etc. */
               
               char * p = find_template_name_end (tokstart + namelen);
               if (p)
                 namelen = p - tokstart;
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

  lexptr += namelen;

  tryname:

  /* Catch specific keywords.  Should be done with a data structure.  */
  switch (namelen)
    {
    case 8:
      if (strncmp (tokstart, "unsigned", 8) == 0)
	return UNSIGNED;
      if ((current_language->la_language == language_cplus
	   || current_language->la_language == language_objcplus)
	  && strncmp (tokstart, "template", 8) == 0)
	return TEMPLATE;
      if (strncmp (tokstart, "volatile", 8) == 0)
	return VOLATILE_KEYWORD;
      break;
    /* EMBARCADERO LOCAL begin MS built-in integer types (__int32, etc) */
    case 7:
      if (strncmp (tokstart, "__int16", 7) == 0)
	return MS_INT16;
      if (strncmp (tokstart, "__int32", 7) == 0)
	return MS_INT32;
      if (strncmp (tokstart, "__int64", 7) == 0)
	return MS_INT64;
      break;
    /* EMBARCADERO LOCAL end MS built-in integer types (__int32, etc) */
    case 6:
      if (strncmp (tokstart, "struct", 6) == 0)
	return STRUCT;
      if (strncmp (tokstart, "signed", 6) == 0)
	return SIGNED_KEYWORD;
      if (strncmp (tokstart, "sizeof", 6) == 0)
	return SIZEOF;
      if (strncmp (tokstart, "double", 6) == 0)
	return DOUBLE_KEYWORD;
      /* EMBARCADERO LOCAL begin MS built-in integer type (__int8) */
      if (strncmp (tokstart, "__int8", 6) == 0)
	return MS_INT8;
      /* EMBARCADERO LOCAL end MS built-in integer type (__int8) */
      break;
    case 5:
      if (current_language->la_language == language_cplus
	   || current_language->la_language == language_objcplus)
        {
          if (strncmp (tokstart, "false", 5) == 0)
            return FALSEKEYWORD;
          if (strncmp (tokstart, "class", 5) == 0)
            return CLASS;
        }
      if (strncmp (tokstart, "union", 5) == 0)
	return UNION;
      if (strncmp (tokstart, "short", 5) == 0)
	return SHORT;
      if (strncmp (tokstart, "const", 5) == 0)
	return CONST_KEYWORD;
      break;
    case 4:
      if (strncmp (tokstart, "enum", 4) == 0)
	return ENUM;
      if (strncmp (tokstart, "long", 4) == 0)
	return LONG;
      if (current_language->la_language == language_cplus
	  || current_language->la_language == language_objcplus)
	{
	  if (strncmp (tokstart, "true", 4) == 0)
	    return TRUEKEYWORD;
	  /* EMBARCADERO LOCAL properties */
	  if (strncmp (tokstart, "this", 4) == 0)
	    return THIS;
	}
      break;
    case 3:
      if (strncmp (tokstart, "int", 3) == 0)
	return INT_KEYWORD;
      break;
    default:
      break;
    }

  yylval.sval.ptr = tokstart;
  yylval.sval.length = namelen;

  if (*tokstart == '$')
    {
      write_dollar_variable (yylval.sval);
      return VARIABLE;
    }
  
  /* Look ahead and see if we can consume more of the input
     string to get a reasonable class/namespace spec or a
     fully-qualified name.  This is a kludge to get around the
     HP aCC compiler's generation of symbol names with embedded
     colons for namespace and nested classes. */

  /* NOTE: carlton/2003-09-24: I don't entirely understand the
     HP-specific code, either here or in linespec.  Having said that,
     I suspect that we're actually moving towards their model: we want
     symbols whose names are fully qualified, which matches the
     description above.  */
  if (unquoted_expr)
    {
      /* EMBARCADERO LOCAL begin trunk merge for wide char support */
      char * token_string = NULL;
      int class_prefix = 0;
      /* EMBARCADERO LOCAL end trunk merge for wide char support */
      /* Only do it if not inside single quotes */ 
      sym_class = parse_nested_classes_for_hpacc (yylval.sval.ptr, yylval.sval.length,
                                                  &token_string, &class_prefix, &lexptr);
      if (sym_class)
        {
          /* Replace the current token with the bigger one we found */ 
          yylval.sval.ptr = token_string;
          yylval.sval.length = strlen (token_string);
        }
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
    int hextype;
    int *need_this;

    if (current_language->la_language == language_cplus
	|| current_language->la_language == language_objc
	|| current_language->la_language == language_objcplus)
      need_this = &is_a_field_of_this;
    else
      need_this = (int *) NULL;
    
    sym = lookup_symbol (tmp, expression_context_block,
			 VAR_DOMAIN, need_this,
			 (struct symtab **) NULL);
    /* Call lookup_symtab, not lookup_partial_symtab, in case there are
       no psymtabs (coff, xcoff, or some future change to blow away the
       psymtabs once once symbols are read).  */
    if (sym && SYMBOL_CLASS (sym) == LOC_BLOCK)
      {
	yylval.ssym.sym = sym;
	yylval.ssym.is_a_field_of_this = is_a_field_of_this;
	return BLOCKNAME;
      }
    else if (!sym)
      {				/* See if it's a file name. */
	struct symtab *symtab;

	symtab = lookup_symtab (tmp);

	if (symtab)
	  {
	    yylval.bval = BLOCKVECTOR_BLOCK (BLOCKVECTOR (symtab), STATIC_BLOCK);
	    return FILENAME;
	  }
      }

    if (sym && SYMBOL_CLASS (sym) == LOC_TYPEDEF)
        {
	  /* NOTE: carlton/2003-09-25: There used to be code here to
	     handle nested types.  It didn't work very well.  See the
	     comment before qualified_type for more info.  */
	  yylval.tsym.type = SYMBOL_TYPE (sym);
	  return TYPENAME;
        }
    yylval.tsym.type
      = language_lookup_primitive_type_by_name (current_language,
						current_gdbarch, tmp);
    if (yylval.tsym.type != NULL)
      return TYPENAME;

    /* APPLE LOCAL: See if it's an ObjC classname.  This was previously inside 
       the "if lookup_struct_typedef" block, but then we wouldn't recognize
       ObjC classes that had no debug info, so it got hoisted out.  This
       results in unfortunate side-effect that gdb is calling into the
       ObjC runtime a lot to see if various no-debug-info symbols are
       classes.  */
    /* APPLE LOCAL begin avoid calling lookup_objc_class unnecessarily.  */
    if (!sym && should_lookup_objc_class ()
	&& square_bracket_seen)  
      {
	extern struct symbol *lookup_struct_typedef ();
        CORE_ADDR Class = lookup_objc_class (tmp);
	square_bracket_seen = 0;
	/* APPLE LOCAL end avoid calling lookup_objc_class unnecessarily.  */
        if (Class)
	  {
	    sym = lookup_struct_typedef (tmp, expression_context_block, 1);
	    if (sym)
	      yylval.class.type = SYMBOL_TYPE (sym);
	    else
	      yylval.class.type = NULL;

	    yylval.class.class = Class;
	    return OBJC_CLASSNAME;
	  }
      }
    
    /* Input names that aren't symbols but ARE valid hex numbers,
       when the input radix permits them, can be names or numbers
       depending on the parse.  Note we support radixes > 16 here.  */
    if (!sym && 
        ((tokstart[0] >= 'a' && tokstart[0] < 'a' + input_radix - 10) ||
         (tokstart[0] >= 'A' && tokstart[0] < 'A' + input_radix - 10)))
      {
 	YYSTYPE newlval;	/* Its value is ignored.  */
	hextype = parse_number (tokstart, namelen, 0, &newlval);
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
    if (in_parse_field && *lexptr == '\0')
      saw_name_at_eof = 1;
    return NAME;
  }
}

int
c_parse (void)
{
  last_was_structop = 0;
  saw_name_at_eof = 0;
  return yyparse ();
}

void
yyerror (msg)
     char *msg;
{
  if (prev_lexptr)
    lexptr = prev_lexptr;

  error ("A %s in expression, near `%s'.", (msg ? msg : "error"), lexptr);
}
