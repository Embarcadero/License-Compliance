/* Generic code for supporting multiple C++ ABI's

   Copyright 2001, 2002, 2003, 2005 Free Software Foundation, Inc.

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
#include "value.h"
#include "cp-abi.h"
#include "command.h"
#include "gdbcmd.h"
#include "ui-out.h"

#include "gdb_string.h"

static struct cp_abi_ops *find_cp_abi (const char *short_name);

static struct cp_abi_ops current_cp_abi = { "", NULL };
static struct cp_abi_ops auto_cp_abi = { "auto", NULL };

#define CP_ABI_MAX 8
static struct cp_abi_ops *cp_abis[CP_ABI_MAX];
static int num_cp_abis = 0;

enum ctor_kinds
is_constructor_name (const char *name)
{
  if ((current_cp_abi.is_constructor_name) == NULL)
    error (_("ABI doesn't define required function is_constructor_name"));
  return (*current_cp_abi.is_constructor_name) (name);
}

enum dtor_kinds
is_destructor_name (const char *name)
{

  /* APPLE LOCAL: For gcc 4.0 DWARF, the PHYSNAME for a destructor is
     the unmangled name.  So this test is going to fail.  Let's just
     check for ~ here.  NOTE, this is a hack, since we really should
     only do this for the gnu-v3 ABI, but that is_destructor_name is
     somewhere over in libiberty, and I don't want to change that...
     Note, also, at this point I have no idea what kind of dtor this
     is but all our callers don't actually care.  */
  enum dtor_kinds retval;

  if ((current_cp_abi.is_destructor_name) == NULL)
    error (_("ABI doesn't define required function is_destructor_name"));
  retval = (*current_cp_abi.is_destructor_name) (name);
  if (!retval && name[0] == '~')
    retval = deleting_dtor;
  return retval;
}

int
is_vtable_name (const char *name)
{
  if ((current_cp_abi.is_vtable_name) == NULL)
    error (_("ABI doesn't define required function is_vtable_name"));
  return (*current_cp_abi.is_vtable_name) (name);
}

int
is_operator_name (const char *name)
{
  if ((current_cp_abi.is_operator_name) == NULL)
    error (_("ABI doesn't define required function is_operator_name"));
  return (*current_cp_abi.is_operator_name) (name);
}

int
baseclass_offset (struct type *type, int index, const bfd_byte *valaddr,
		  CORE_ADDR address)
{
  if (current_cp_abi.baseclass_offset == NULL)
    error (_("ABI doesn't define required function baseclass_offset"));
  return (*current_cp_abi.baseclass_offset) (type, index, valaddr, address);
}

struct value *
value_virtual_fn_field (struct value **arg1p, struct fn_field *f, int j,
			struct type *type, int offset)
{
  if ((current_cp_abi.virtual_fn_field) == NULL)
    return NULL;
  return (*current_cp_abi.virtual_fn_field) (arg1p, f, j, type, offset);
}

struct type *
value_rtti_type (struct value *v, int *full, int *top, int *using_enc)
{
  if ((current_cp_abi.rtti_type) == NULL)
    return NULL;
  return (*current_cp_abi.rtti_type) (v, full, top, using_enc);
}

void
cplus_print_method_ptr (const gdb_byte *contents, struct type *type,
			struct ui_file *stream)
{
  if (current_cp_abi.print_method_ptr == NULL)
    error (_("GDB does not support pointers to methods on this target"));
  (*current_cp_abi.print_method_ptr) (contents, type, stream);
}

int
cplus_method_ptr_size (void)
{
  if (current_cp_abi.method_ptr_size == NULL)
    error (_("GDB does not support pointers to methods on this target"));
  return (*current_cp_abi.method_ptr_size) ();
}

void
cplus_make_method_ptr (gdb_byte *contents, CORE_ADDR value, int is_virtual)
{
  if (current_cp_abi.make_method_ptr == NULL)
    error (_("GDB does not support pointers to methods on this target"));
  (*current_cp_abi.make_method_ptr) (contents, value, is_virtual);
}

struct value *
cplus_method_ptr_to_value (struct value **this_p, struct value *method_ptr)
{
  if (current_cp_abi.method_ptr_to_value == NULL)
    error (_("GDB does not support pointers to methods on this target"));
  return (*current_cp_abi.method_ptr_to_value) (this_p, method_ptr);
}

int
cp_pass_by_reference (struct type *type)
{
  if ((current_cp_abi.pass_by_reference) == NULL)
    return 0;
  return (*current_cp_abi.pass_by_reference) (type);
}

/* Set the current C++ ABI to SHORT_NAME.  */

static int
switch_to_cp_abi (const char *short_name)
{
  struct cp_abi_ops *abi;

  abi = find_cp_abi (short_name);
  if (abi == NULL)
    return 0;

  current_cp_abi = *abi;
  return 1;
}

/* Add ABI to the list of supported C++ ABI's.  */

int
register_cp_abi (struct cp_abi_ops *abi)
{
  if (num_cp_abis == CP_ABI_MAX)
    internal_error (__FILE__, __LINE__,
		    _("Too many C++ ABIs, please increase CP_ABI_MAX in cp-abi.c"));

  cp_abis[num_cp_abis++] = abi;

  return 1;
}

/* Set the ABI to use in "auto" mode to SHORT_NAME.  */

void
set_cp_abi_as_auto_default (const char *short_name)
{
  char *new_longname, *new_doc;
  struct cp_abi_ops *abi = find_cp_abi (short_name);

  if (abi == NULL)
    internal_error (__FILE__, __LINE__,
		    _("Cannot find C++ ABI \"%s\" to set it as auto default."),
		    short_name);

  if (auto_cp_abi.longname != NULL)
    xfree ((char *) auto_cp_abi.longname);
  if (auto_cp_abi.doc != NULL)
    xfree ((char *) auto_cp_abi.doc);

  auto_cp_abi = *abi;

  auto_cp_abi.shortname = "auto";
  xasprintf (&new_longname, "currently \"%s\"", abi->shortname);
  auto_cp_abi.longname = new_longname;

  xasprintf (&new_doc, "Automatically selected; currently \"%s\"",
	     abi->shortname);
  auto_cp_abi.doc = new_doc;

  /* Since we copy the current ABI into current_cp_abi instead of
     using a pointer, if auto is currently the default, we need to
     reset it.  */
  if (strcmp (current_cp_abi.shortname, "auto") == 0)
    switch_to_cp_abi ("auto");
}

/* APPLE LOCAL begin C++ auto abi */
int
cp_abi_is_auto_p ()
{
  if (strcmp (current_cp_abi.shortname, "auto") == 0)
    return 1;
  else
    return 0;
}
/* APPLE LOCAL end C++ auto abi */

/* Return the ABI operations associated with SHORT_NAME.  */

static struct cp_abi_ops *
find_cp_abi (const char *short_name)
{
  int i;

  for (i = 0; i < num_cp_abis; i++)
    if (strcmp (cp_abis[i]->shortname, short_name) == 0)
      return cp_abis[i];

  return NULL;
}

/* Display the list of registered C++ ABIs.  */

static void
list_cp_abis (int from_tty)
{
  struct cleanup *cleanup_chain;
  int i;
  ui_out_text (uiout, "The available C++ ABIs are:\n");

  cleanup_chain = make_cleanup_ui_out_tuple_begin_end (uiout, "cp-abi-list");
  for (i = 0; i < num_cp_abis; i++)
    {
      char pad[14];
      int padcount;

      ui_out_text (uiout, "  ");
      ui_out_field_string (uiout, "cp-abi", cp_abis[i]->shortname);

      padcount = 16 - 2 - strlen (cp_abis[i]->shortname);
      pad[padcount] = 0;
      while (padcount > 0)
	pad[--padcount] = ' ';
      ui_out_text (uiout, pad);

      ui_out_field_string (uiout, "doc", cp_abis[i]->doc);
      ui_out_text (uiout, "\n");
    }
  do_cleanups (cleanup_chain);
}

/* Set the current C++ ABI, or display the list of options if no
   argument is given.  */

static void
set_cp_abi_cmd (char *args, int from_tty)
{
  if (args == NULL)
    {
      list_cp_abis (from_tty);
      return;
    }

  if (!switch_to_cp_abi (args))
    error (_("Could not find \"%s\" in ABI list"), args);
}

/* Show the currently selected C++ ABI.  */

static void
show_cp_abi_cmd (char *args, int from_tty)
{
  ui_out_text (uiout, "The currently selected C++ ABI is \"");

  ui_out_field_string (uiout, "cp-abi", current_cp_abi.shortname);
  ui_out_text (uiout, "\" (");
  ui_out_field_string (uiout, "longname", current_cp_abi.longname);
  ui_out_text (uiout, ").\n");
}

extern initialize_file_ftype _initialize_cp_abi; /* -Wmissing-prototypes */

void
_initialize_cp_abi (void)
{
  register_cp_abi (&auto_cp_abi);
  switch_to_cp_abi ("auto");

  add_cmd ("cp-abi", class_obscure, set_cp_abi_cmd, _("\
Set the ABI used for inspecting C++ objects.\n\
\"set cp-abi\" with no arguments will list the available ABIs."),
	   &setlist);

  add_cmd ("cp-abi", class_obscure, show_cp_abi_cmd,
	   _("Show the ABI used for inspecting C++ objects."), &showlist);
}
