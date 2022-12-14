/* Helper routines for C++ support in GDB.
   Copyright 2002, 2003, 2004, 2005 Free Software Foundation, Inc.

   Contributed by MontaVista Software.
   Namespace support contributed by David Carlton.

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

#ifndef CP_SUPPORT_H
#define CP_SUPPORT_H

/* We need this for 'domain_enum', alas...  */

#include "symtab.h"

/* Opaque declarations.  */

struct symbol;
struct obstack;
struct block;
struct objfile;
struct type;
struct demangle_component;

/* This struct is designed to store data from using directives.  It
   says that names from namespace IMPORT_SRC should be visible within
   namespace IMPORT_DEST.  These form a linked list; NEXT is the next element
   of the list.  If the imported namespace has been aliased, ALIAS is set to a
   string representing the alias.  Otherwise, ALIAS is NULL.
   Eg:
       namespace C = A::B;
   ALIAS = "C"
*/

struct using_direct
{
  char *import_src;
  char *import_dest;

  char *alias;

  struct using_direct *next;

  /* Used during import search to temporarily mark this node as searched.  */
  int searched;
};


/* Functions from cp-support.c.  */

extern char *cp_canonicalize_string (const char *string);

extern char *cp_class_name_from_physname (const char *physname);

extern char *method_name_from_physname (const char *physname);

extern char *cp_remove_params (const char *demangled_name);

extern unsigned int cp_find_first_component (const char *name);

extern unsigned int cp_entire_prefix_len (const char *name);

extern char *cp_func_name (const char *full_name);

extern struct symbol **make_symbol_overload_list (const char *,
						  const char *);

extern struct type *cp_lookup_rtti_type (const char *name,
					 struct block *block);

/* Functions/variables from cp-namespace.c.  */

extern int cp_is_anonymous (const char *namespace);

extern void cp_add_using_directive (const char *dest,
                                    const char *src,
                                    const char *alias,
                                    struct obstack *obstack);

extern void cp_initialize_namespace (void);

extern void cp_finalize_namespace (struct block *static_block,
				   struct obstack *obstack);

extern void cp_set_block_scope (const struct symbol *symbol,
				struct block *block,
				struct obstack *obstack,
				const char *processing_current_prefix,
				int processing_has_namespace_info);

extern void cp_scan_for_anonymous_namespaces (const struct symbol *symbol,
					      /* EMBARCADERO LOCAL: pass obstack */
					      struct obstack *obstack);

extern struct symbol *cp_lookup_symbol_nonlocal (const char *name,
						 const char *linkage_name,
						 const struct block *block,
						 const domain_enum domain,
						 struct symtab **symtab);

extern struct symbol *cp_lookup_symbol_namespace (const char *namespace,
						  const char *name,
						  const char *linkage_name,
						  const struct block *block,
						  const domain_enum domain,
						  const int search_parents, 
						  struct symtab **symtab);

extern struct type *cp_lookup_nested_type (struct type *parent_type,
					   const char *nested_name,
					   const struct block *block);

extern void cp_check_possible_namespace_symbols (const char *name,
						 struct objfile *objfile);

struct type *cp_lookup_transparent_type (const char *name);

/* EMBARCADERO LOCAL begin Delphi */
/* Warppers to functions from *-name-parser.y.  */

extern struct demangle_component *demangled_name_to_comp
  (const char *demangled_name, void **memory_p, const char **errmsg);

extern char *comp_to_string (struct demangle_component *result,
			     int estimated_len);
/* EMBARCADERO LOCAL end Delphi */

/* Functions from cp-name-parser.y.  */

extern struct demangle_component *cp_demangled_name_to_comp
  (const char *demangled_name, void **memory_p, const char **errmsg);

extern char *cp_comp_to_string (struct demangle_component *result,
				int estimated_len);

/* EMBARCADERO LOCAL begin Delphi */
/* Functions from p-name-parser.y.  */

extern struct demangle_component *p_demangled_name_to_comp
  (const char *demangled_name, void **memory_p, const char **errmsg);

extern char *p_comp_to_string (struct demangle_component *result,
			       int estimated_len);
/* EMBARCADERO LOCAL end Delphi */

/* The list of "maint cplus" commands.  */

extern struct cmd_list_element *maint_cplus_cmd_list;

/* Pointer to member function.  Depends on compiler implementation.  */

#if 0 /* should junk this */
#define METHOD_PTR_IS_VIRTUAL(ADDR)  ((ADDR) & 0x80000000)
#define METHOD_PTR_FROM_VOFFSET(OFFSET) (0x80000000 + (OFFSET))
#define METHOD_PTR_TO_VOFFSET(ADDR) (~0x80000000 & (ADDR))
#endif

#endif /* CP_SUPPORT_H */
