/* *INDENT-OFF* */ /* THIS FILE IS GENERATED */

/* Dynamic architecture support for GDB, the GNU debugger.

   Copyright 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005 Free
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

/* This file was created with the aid of ``gdbarch.sh''.

   The Bourne shell script ``gdbarch.sh'' creates the files
   ``new-gdbarch.c'' and ``new-gdbarch.h and then compares them
   against the existing ``gdbarch.[hc]''.  Any differences found
   being reported.

   If editing this file, please also run gdbarch.sh and merge any
   changes into that script. Conversely, when making sweeping changes
   to this file, modifying gdbarch.sh and using its output may prove
   easier. */

#ifndef GDBARCH_H
#define GDBARCH_H

struct address_context;
struct floatformat;
struct ui_file;
struct frame_info;
struct value;
struct objfile;
struct minimal_symbol;
struct regcache;
struct reggroup;
struct regset;
struct disassemble_info;
struct target_ops;
struct obstack;

extern struct gdbarch *current_gdbarch;


/* The following are pre-initialized by GDBARCH. */

extern const struct bfd_arch_info * gdbarch_bfd_arch_info (struct gdbarch *gdbarch);
/* set_gdbarch_bfd_arch_info() - not applicable - pre-initialized. */
#if !defined (GDB_TM_FILE) && defined (TARGET_ARCHITECTURE)
#error "Non multi-arch definition of TARGET_ARCHITECTURE"
#endif
#if !defined (TARGET_ARCHITECTURE)
#define TARGET_ARCHITECTURE (gdbarch_bfd_arch_info (current_gdbarch))
#endif

extern int gdbarch_byte_order (struct gdbarch *gdbarch);
/* set_gdbarch_byte_order() - not applicable - pre-initialized. */
#if !defined (GDB_TM_FILE) && defined (TARGET_BYTE_ORDER)
#error "Non multi-arch definition of TARGET_BYTE_ORDER"
#endif
#if !defined (TARGET_BYTE_ORDER)
#define TARGET_BYTE_ORDER (gdbarch_byte_order (current_gdbarch))
#endif

extern enum gdb_osabi gdbarch_osabi (struct gdbarch *gdbarch);
/* set_gdbarch_osabi() - not applicable - pre-initialized. */
#if !defined (GDB_TM_FILE) && defined (TARGET_OSABI)
#error "Non multi-arch definition of TARGET_OSABI"
#endif
#if !defined (TARGET_OSABI)
#define TARGET_OSABI (gdbarch_osabi (current_gdbarch))
#endif


/* The following are initialized by the target dependent code. */

/* Number of bits in a char or unsigned char for the target machine.
   Just like CHAR_BIT in <limits.h> but describes the target machine.
   v:TARGET_CHAR_BIT:int:char_bit::::8 * sizeof (char):8::0:
  
   Number of bits in a short or unsigned short for the target machine. */

extern int gdbarch_short_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_short_bit (struct gdbarch *gdbarch, int short_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_SHORT_BIT)
#error "Non multi-arch definition of TARGET_SHORT_BIT"
#endif
#if !defined (TARGET_SHORT_BIT)
#define TARGET_SHORT_BIT (gdbarch_short_bit (current_gdbarch))
#endif

/* Number of bits in an int or unsigned int for the target machine. */

extern int gdbarch_int_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_int_bit (struct gdbarch *gdbarch, int int_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_INT_BIT)
#error "Non multi-arch definition of TARGET_INT_BIT"
#endif
#if !defined (TARGET_INT_BIT)
#define TARGET_INT_BIT (gdbarch_int_bit (current_gdbarch))
#endif

/* Number of bits in a long or unsigned long for the target machine. */

extern int gdbarch_long_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_long_bit (struct gdbarch *gdbarch, int long_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_LONG_BIT)
#error "Non multi-arch definition of TARGET_LONG_BIT"
#endif
#if !defined (TARGET_LONG_BIT)
#define TARGET_LONG_BIT (gdbarch_long_bit (current_gdbarch))
#endif

/* Number of bits in a long long or unsigned long long for the target
   machine. */

extern int gdbarch_long_long_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_long_long_bit (struct gdbarch *gdbarch, int long_long_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_LONG_LONG_BIT)
#error "Non multi-arch definition of TARGET_LONG_LONG_BIT"
#endif
#if !defined (TARGET_LONG_LONG_BIT)
#define TARGET_LONG_LONG_BIT (gdbarch_long_long_bit (current_gdbarch))
#endif

/* The ABI default bit-size and format for "float", "double", and "long
   double".  These bit/format pairs should eventually be combined into
   a single object.  For the moment, just initialize them as a pair. */

extern int gdbarch_float_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_float_bit (struct gdbarch *gdbarch, int float_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_FLOAT_BIT)
#error "Non multi-arch definition of TARGET_FLOAT_BIT"
#endif
#if !defined (TARGET_FLOAT_BIT)
#define TARGET_FLOAT_BIT (gdbarch_float_bit (current_gdbarch))
#endif

extern const struct floatformat * gdbarch_float_format (struct gdbarch *gdbarch);
extern void set_gdbarch_float_format (struct gdbarch *gdbarch, const struct floatformat * float_format);
#if !defined (GDB_TM_FILE) && defined (TARGET_FLOAT_FORMAT)
#error "Non multi-arch definition of TARGET_FLOAT_FORMAT"
#endif
#if !defined (TARGET_FLOAT_FORMAT)
#define TARGET_FLOAT_FORMAT (gdbarch_float_format (current_gdbarch))
#endif

extern int gdbarch_double_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_double_bit (struct gdbarch *gdbarch, int double_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_DOUBLE_BIT)
#error "Non multi-arch definition of TARGET_DOUBLE_BIT"
#endif
#if !defined (TARGET_DOUBLE_BIT)
#define TARGET_DOUBLE_BIT (gdbarch_double_bit (current_gdbarch))
#endif

extern const struct floatformat * gdbarch_double_format (struct gdbarch *gdbarch);
extern void set_gdbarch_double_format (struct gdbarch *gdbarch, const struct floatformat * double_format);
#if !defined (GDB_TM_FILE) && defined (TARGET_DOUBLE_FORMAT)
#error "Non multi-arch definition of TARGET_DOUBLE_FORMAT"
#endif
#if !defined (TARGET_DOUBLE_FORMAT)
#define TARGET_DOUBLE_FORMAT (gdbarch_double_format (current_gdbarch))
#endif

extern int gdbarch_long_double_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_long_double_bit (struct gdbarch *gdbarch, int long_double_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_LONG_DOUBLE_BIT)
#error "Non multi-arch definition of TARGET_LONG_DOUBLE_BIT"
#endif
#if !defined (TARGET_LONG_DOUBLE_BIT)
#define TARGET_LONG_DOUBLE_BIT (gdbarch_long_double_bit (current_gdbarch))
#endif

extern const struct floatformat * gdbarch_long_double_format (struct gdbarch *gdbarch);
extern void set_gdbarch_long_double_format (struct gdbarch *gdbarch, const struct floatformat * long_double_format);
#if !defined (GDB_TM_FILE) && defined (TARGET_LONG_DOUBLE_FORMAT)
#error "Non multi-arch definition of TARGET_LONG_DOUBLE_FORMAT"
#endif
#if !defined (TARGET_LONG_DOUBLE_FORMAT)
#define TARGET_LONG_DOUBLE_FORMAT (gdbarch_long_double_format (current_gdbarch))
#endif

/* For most targets, a pointer on the target and its representation as an
   address in GDB have the same size and "look the same".  For such a
   target, you need only set TARGET_PTR_BIT / ptr_bit and TARGET_ADDR_BIT
   / addr_bit will be set from it.
  
   If TARGET_PTR_BIT and TARGET_ADDR_BIT are different, you'll probably
   also need to set POINTER_TO_ADDRESS and ADDRESS_TO_POINTER as well.
  
   ptr_bit is the size of a pointer on the target */

extern int gdbarch_ptr_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_ptr_bit (struct gdbarch *gdbarch, int ptr_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_PTR_BIT)
#error "Non multi-arch definition of TARGET_PTR_BIT"
#endif
#if !defined (TARGET_PTR_BIT)
#define TARGET_PTR_BIT (gdbarch_ptr_bit (current_gdbarch))
#endif

/* addr_bit is the size of a target address as represented in gdb */

extern int gdbarch_addr_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_addr_bit (struct gdbarch *gdbarch, int addr_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_ADDR_BIT)
#error "Non multi-arch definition of TARGET_ADDR_BIT"
#endif
#if !defined (TARGET_ADDR_BIT)
#define TARGET_ADDR_BIT (gdbarch_addr_bit (current_gdbarch))
#endif

/* Number of bits in a BFD_VMA for the target object file format. */

extern int gdbarch_bfd_vma_bit (struct gdbarch *gdbarch);
extern void set_gdbarch_bfd_vma_bit (struct gdbarch *gdbarch, int bfd_vma_bit);
#if !defined (GDB_TM_FILE) && defined (TARGET_BFD_VMA_BIT)
#error "Non multi-arch definition of TARGET_BFD_VMA_BIT"
#endif
#if !defined (TARGET_BFD_VMA_BIT)
#define TARGET_BFD_VMA_BIT (gdbarch_bfd_vma_bit (current_gdbarch))
#endif

/* One if `char' acts like `signed char', zero if `unsigned char'. */

extern int gdbarch_char_signed (struct gdbarch *gdbarch);
extern void set_gdbarch_char_signed (struct gdbarch *gdbarch, int char_signed);
#if !defined (GDB_TM_FILE) && defined (TARGET_CHAR_SIGNED)
#error "Non multi-arch definition of TARGET_CHAR_SIGNED"
#endif
#if !defined (TARGET_CHAR_SIGNED)
#define TARGET_CHAR_SIGNED (gdbarch_char_signed (current_gdbarch))
#endif

#if defined (TARGET_READ_PC)
/* Legacy for systems yet to multi-arch TARGET_READ_PC */
#if !defined (TARGET_READ_PC_P)
#define TARGET_READ_PC_P() (1)
#endif
#endif

extern int gdbarch_read_pc_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (TARGET_READ_PC_P)
#error "Non multi-arch definition of TARGET_READ_PC"
#endif
#if !defined (TARGET_READ_PC_P)
#define TARGET_READ_PC_P() (gdbarch_read_pc_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_read_pc_ftype) (ptid_t ptid);
extern CORE_ADDR gdbarch_read_pc (struct gdbarch *gdbarch, ptid_t ptid);
extern void set_gdbarch_read_pc (struct gdbarch *gdbarch, gdbarch_read_pc_ftype *read_pc);
#if !defined (GDB_TM_FILE) && defined (TARGET_READ_PC)
#error "Non multi-arch definition of TARGET_READ_PC"
#endif
#if !defined (TARGET_READ_PC)
#define TARGET_READ_PC(ptid) (gdbarch_read_pc (current_gdbarch, ptid))
#endif

typedef void (gdbarch_write_pc_ftype) (CORE_ADDR val, ptid_t ptid);
extern void gdbarch_write_pc (struct gdbarch *gdbarch, CORE_ADDR val, ptid_t ptid);
extern void set_gdbarch_write_pc (struct gdbarch *gdbarch, gdbarch_write_pc_ftype *write_pc);
#if !defined (GDB_TM_FILE) && defined (TARGET_WRITE_PC)
#error "Non multi-arch definition of TARGET_WRITE_PC"
#endif
#if !defined (TARGET_WRITE_PC)
#define TARGET_WRITE_PC(val, ptid) (gdbarch_write_pc (current_gdbarch, val, ptid))
#endif

/* UNWIND_SP is a direct replacement for TARGET_READ_SP. */

#if defined (TARGET_READ_SP)
/* Legacy for systems yet to multi-arch TARGET_READ_SP */
#if !defined (TARGET_READ_SP_P)
#define TARGET_READ_SP_P() (1)
#endif
#endif

extern int gdbarch_read_sp_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (TARGET_READ_SP_P)
#error "Non multi-arch definition of TARGET_READ_SP"
#endif
#if !defined (TARGET_READ_SP_P)
#define TARGET_READ_SP_P() (gdbarch_read_sp_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_read_sp_ftype) (void);
extern CORE_ADDR gdbarch_read_sp (struct gdbarch *gdbarch);
extern void set_gdbarch_read_sp (struct gdbarch *gdbarch, gdbarch_read_sp_ftype *read_sp);
#if !defined (GDB_TM_FILE) && defined (TARGET_READ_SP)
#error "Non multi-arch definition of TARGET_READ_SP"
#endif
#if !defined (TARGET_READ_SP)
#define TARGET_READ_SP() (gdbarch_read_sp (current_gdbarch))
#endif

/* Function for getting target's idea of a frame pointer.  FIXME: GDB's
   whole scheme for dealing with "frames" and "frame pointers" needs a
   serious shakedown. */

typedef void (gdbarch_virtual_frame_pointer_ftype) (CORE_ADDR pc, int *frame_regnum, LONGEST *frame_offset);
extern void gdbarch_virtual_frame_pointer (struct gdbarch *gdbarch, CORE_ADDR pc, int *frame_regnum, LONGEST *frame_offset);
extern void set_gdbarch_virtual_frame_pointer (struct gdbarch *gdbarch, gdbarch_virtual_frame_pointer_ftype *virtual_frame_pointer);
#if !defined (GDB_TM_FILE) && defined (TARGET_VIRTUAL_FRAME_POINTER)
#error "Non multi-arch definition of TARGET_VIRTUAL_FRAME_POINTER"
#endif
#if !defined (TARGET_VIRTUAL_FRAME_POINTER)
#define TARGET_VIRTUAL_FRAME_POINTER(pc, frame_regnum, frame_offset) (gdbarch_virtual_frame_pointer (current_gdbarch, pc, frame_regnum, frame_offset))
#endif

extern int gdbarch_pseudo_register_read_p (struct gdbarch *gdbarch);

typedef void (gdbarch_pseudo_register_read_ftype) (struct gdbarch *gdbarch, struct regcache *regcache, int cookednum, gdb_byte *buf);
extern void gdbarch_pseudo_register_read (struct gdbarch *gdbarch, struct regcache *regcache, int cookednum, gdb_byte *buf);
extern void set_gdbarch_pseudo_register_read (struct gdbarch *gdbarch, gdbarch_pseudo_register_read_ftype *pseudo_register_read);

extern int gdbarch_pseudo_register_write_p (struct gdbarch *gdbarch);

typedef void (gdbarch_pseudo_register_write_ftype) (struct gdbarch *gdbarch, struct regcache *regcache, int cookednum, const gdb_byte *buf);
extern void gdbarch_pseudo_register_write (struct gdbarch *gdbarch, struct regcache *regcache, int cookednum, const gdb_byte *buf);
extern void set_gdbarch_pseudo_register_write (struct gdbarch *gdbarch, gdbarch_pseudo_register_write_ftype *pseudo_register_write);

extern int gdbarch_num_regs (struct gdbarch *gdbarch);
extern void set_gdbarch_num_regs (struct gdbarch *gdbarch, int num_regs);
#if !defined (GDB_TM_FILE) && defined (NUM_REGS)
#error "Non multi-arch definition of NUM_REGS"
#endif
#if !defined (NUM_REGS)
#define NUM_REGS (gdbarch_num_regs (current_gdbarch))
#endif

/* This macro gives the number of pseudo-registers that live in the
   register namespace but do not get fetched or stored on the target.
   These pseudo-registers may be aliases for other registers,
   combinations of other registers, or they may be computed by GDB. */

extern int gdbarch_num_pseudo_regs (struct gdbarch *gdbarch);
extern void set_gdbarch_num_pseudo_regs (struct gdbarch *gdbarch, int num_pseudo_regs);
#if !defined (GDB_TM_FILE) && defined (NUM_PSEUDO_REGS)
#error "Non multi-arch definition of NUM_PSEUDO_REGS"
#endif
#if !defined (NUM_PSEUDO_REGS)
#define NUM_PSEUDO_REGS (gdbarch_num_pseudo_regs (current_gdbarch))
#endif

/* GDB's standard (or well known) register numbers.  These can map onto
   a real register or a pseudo (computed) register or not be defined at
   all (-1).
   SP_REGNUM will hopefully be replaced by UNWIND_SP. */

extern int gdbarch_sp_regnum (struct gdbarch *gdbarch);
extern void set_gdbarch_sp_regnum (struct gdbarch *gdbarch, int sp_regnum);
#if !defined (GDB_TM_FILE) && defined (SP_REGNUM)
#error "Non multi-arch definition of SP_REGNUM"
#endif
#if !defined (SP_REGNUM)
#define SP_REGNUM (gdbarch_sp_regnum (current_gdbarch))
#endif

extern int gdbarch_pc_regnum (struct gdbarch *gdbarch);
extern void set_gdbarch_pc_regnum (struct gdbarch *gdbarch, int pc_regnum);
#if !defined (GDB_TM_FILE) && defined (PC_REGNUM)
#error "Non multi-arch definition of PC_REGNUM"
#endif
#if !defined (PC_REGNUM)
#define PC_REGNUM (gdbarch_pc_regnum (current_gdbarch))
#endif

extern int gdbarch_ps_regnum (struct gdbarch *gdbarch);
extern void set_gdbarch_ps_regnum (struct gdbarch *gdbarch, int ps_regnum);
#if !defined (GDB_TM_FILE) && defined (PS_REGNUM)
#error "Non multi-arch definition of PS_REGNUM"
#endif
#if !defined (PS_REGNUM)
#define PS_REGNUM (gdbarch_ps_regnum (current_gdbarch))
#endif

extern int gdbarch_fp0_regnum (struct gdbarch *gdbarch);
extern void set_gdbarch_fp0_regnum (struct gdbarch *gdbarch, int fp0_regnum);
#if !defined (GDB_TM_FILE) && defined (FP0_REGNUM)
#error "Non multi-arch definition of FP0_REGNUM"
#endif
#if !defined (FP0_REGNUM)
#define FP0_REGNUM (gdbarch_fp0_regnum (current_gdbarch))
#endif

/* Convert stab register number (from `r' declaration) to a gdb REGNUM. */

typedef int (gdbarch_stab_reg_to_regnum_ftype) (int stab_regnr);
extern int gdbarch_stab_reg_to_regnum (struct gdbarch *gdbarch, int stab_regnr);
extern void set_gdbarch_stab_reg_to_regnum (struct gdbarch *gdbarch, gdbarch_stab_reg_to_regnum_ftype *stab_reg_to_regnum);
#if !defined (GDB_TM_FILE) && defined (STAB_REG_TO_REGNUM)
#error "Non multi-arch definition of STAB_REG_TO_REGNUM"
#endif
#if !defined (STAB_REG_TO_REGNUM)
#define STAB_REG_TO_REGNUM(stab_regnr) (gdbarch_stab_reg_to_regnum (current_gdbarch, stab_regnr))
#endif

/* Provide a default mapping from a ecoff register number to a gdb REGNUM. */

typedef int (gdbarch_ecoff_reg_to_regnum_ftype) (int ecoff_regnr);
extern int gdbarch_ecoff_reg_to_regnum (struct gdbarch *gdbarch, int ecoff_regnr);
extern void set_gdbarch_ecoff_reg_to_regnum (struct gdbarch *gdbarch, gdbarch_ecoff_reg_to_regnum_ftype *ecoff_reg_to_regnum);
#if !defined (GDB_TM_FILE) && defined (ECOFF_REG_TO_REGNUM)
#error "Non multi-arch definition of ECOFF_REG_TO_REGNUM"
#endif
#if !defined (ECOFF_REG_TO_REGNUM)
#define ECOFF_REG_TO_REGNUM(ecoff_regnr) (gdbarch_ecoff_reg_to_regnum (current_gdbarch, ecoff_regnr))
#endif

/* Provide a default mapping from a DWARF register number to a gdb REGNUM. */

typedef int (gdbarch_dwarf_reg_to_regnum_ftype) (int dwarf_regnr);
extern int gdbarch_dwarf_reg_to_regnum (struct gdbarch *gdbarch, int dwarf_regnr);
extern void set_gdbarch_dwarf_reg_to_regnum (struct gdbarch *gdbarch, gdbarch_dwarf_reg_to_regnum_ftype *dwarf_reg_to_regnum);
#if !defined (GDB_TM_FILE) && defined (DWARF_REG_TO_REGNUM)
#error "Non multi-arch definition of DWARF_REG_TO_REGNUM"
#endif
#if !defined (DWARF_REG_TO_REGNUM)
#define DWARF_REG_TO_REGNUM(dwarf_regnr) (gdbarch_dwarf_reg_to_regnum (current_gdbarch, dwarf_regnr))
#endif

/* Convert from an sdb register number to an internal gdb register number. */

typedef int (gdbarch_sdb_reg_to_regnum_ftype) (int sdb_regnr);
extern int gdbarch_sdb_reg_to_regnum (struct gdbarch *gdbarch, int sdb_regnr);
extern void set_gdbarch_sdb_reg_to_regnum (struct gdbarch *gdbarch, gdbarch_sdb_reg_to_regnum_ftype *sdb_reg_to_regnum);
#if !defined (GDB_TM_FILE) && defined (SDB_REG_TO_REGNUM)
#error "Non multi-arch definition of SDB_REG_TO_REGNUM"
#endif
#if !defined (SDB_REG_TO_REGNUM)
#define SDB_REG_TO_REGNUM(sdb_regnr) (gdbarch_sdb_reg_to_regnum (current_gdbarch, sdb_regnr))
#endif

typedef int (gdbarch_dwarf2_reg_to_regnum_ftype) (int dwarf2_regnr);
extern int gdbarch_dwarf2_reg_to_regnum (struct gdbarch *gdbarch, int dwarf2_regnr);
extern void set_gdbarch_dwarf2_reg_to_regnum (struct gdbarch *gdbarch, gdbarch_dwarf2_reg_to_regnum_ftype *dwarf2_reg_to_regnum);
#if !defined (GDB_TM_FILE) && defined (DWARF2_REG_TO_REGNUM)
#error "Non multi-arch definition of DWARF2_REG_TO_REGNUM"
#endif
#if !defined (DWARF2_REG_TO_REGNUM)
#define DWARF2_REG_TO_REGNUM(dwarf2_regnr) (gdbarch_dwarf2_reg_to_regnum (current_gdbarch, dwarf2_regnr))
#endif

typedef const char * (gdbarch_register_name_ftype) (int regnr);
extern const char * gdbarch_register_name (struct gdbarch *gdbarch, int regnr);
extern void set_gdbarch_register_name (struct gdbarch *gdbarch, gdbarch_register_name_ftype *register_name);
#if !defined (GDB_TM_FILE) && defined (REGISTER_NAME)
#error "Non multi-arch definition of REGISTER_NAME"
#endif
#if !defined (REGISTER_NAME)
#define REGISTER_NAME(regnr) (gdbarch_register_name (current_gdbarch, regnr))
#endif

/* REGISTER_TYPE is a direct replacement for DEPRECATED_REGISTER_VIRTUAL_TYPE. */

extern int gdbarch_register_type_p (struct gdbarch *gdbarch);

typedef struct type * (gdbarch_register_type_ftype) (struct gdbarch *gdbarch, int reg_nr);
extern struct type * gdbarch_register_type (struct gdbarch *gdbarch, int reg_nr);
extern void set_gdbarch_register_type (struct gdbarch *gdbarch, gdbarch_register_type_ftype *register_type);

/* If the value returned by DEPRECATED_REGISTER_BYTE agrees with the
   register offsets computed using just REGISTER_TYPE, this can be
   deleted.  See: maint print registers.  NOTE: cagney/2002-05-02: This
   function with predicate has a valid (callable) initial value.  As a
   consequence, even when the predicate is false, the corresponding
   function works.  This simplifies the migration process - old code,
   calling DEPRECATED_REGISTER_BYTE, doesn't need to be modified. */

#if defined (DEPRECATED_REGISTER_BYTE)
/* Legacy for systems yet to multi-arch DEPRECATED_REGISTER_BYTE */
#if !defined (DEPRECATED_REGISTER_BYTE_P)
#define DEPRECATED_REGISTER_BYTE_P() (1)
#endif
#endif

extern int gdbarch_deprecated_register_byte_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_REGISTER_BYTE_P)
#error "Non multi-arch definition of DEPRECATED_REGISTER_BYTE"
#endif
#if !defined (DEPRECATED_REGISTER_BYTE_P)
#define DEPRECATED_REGISTER_BYTE_P() (gdbarch_deprecated_register_byte_p (current_gdbarch))
#endif

typedef int (gdbarch_deprecated_register_byte_ftype) (int reg_nr);
extern int gdbarch_deprecated_register_byte (struct gdbarch *gdbarch, int reg_nr);
extern void set_gdbarch_deprecated_register_byte (struct gdbarch *gdbarch, gdbarch_deprecated_register_byte_ftype *deprecated_register_byte);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_REGISTER_BYTE)
#error "Non multi-arch definition of DEPRECATED_REGISTER_BYTE"
#endif
#if !defined (DEPRECATED_REGISTER_BYTE)
#define DEPRECATED_REGISTER_BYTE(reg_nr) (gdbarch_deprecated_register_byte (current_gdbarch, reg_nr))
#endif

/* See gdbint.texinfo, and PUSH_DUMMY_CALL. */

extern int gdbarch_unwind_dummy_id_p (struct gdbarch *gdbarch);

typedef struct frame_id (gdbarch_unwind_dummy_id_ftype) (struct gdbarch *gdbarch, struct frame_info *info);
extern struct frame_id gdbarch_unwind_dummy_id (struct gdbarch *gdbarch, struct frame_info *info);
extern void set_gdbarch_unwind_dummy_id (struct gdbarch *gdbarch, gdbarch_unwind_dummy_id_ftype *unwind_dummy_id);

/* Implement UNWIND_DUMMY_ID and PUSH_DUMMY_CALL, then delete
   DEPRECATED_FP_REGNUM. */

extern int gdbarch_deprecated_fp_regnum (struct gdbarch *gdbarch);
extern void set_gdbarch_deprecated_fp_regnum (struct gdbarch *gdbarch, int deprecated_fp_regnum);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_FP_REGNUM)
#error "Non multi-arch definition of DEPRECATED_FP_REGNUM"
#endif
#if !defined (DEPRECATED_FP_REGNUM)
#define DEPRECATED_FP_REGNUM (gdbarch_deprecated_fp_regnum (current_gdbarch))
#endif

/* See gdbint.texinfo.  See infcall.c. */

extern int gdbarch_push_dummy_call_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_push_dummy_call_ftype) (struct gdbarch *gdbarch, struct value *function, struct regcache *regcache, CORE_ADDR bp_addr, int nargs, struct value **args, CORE_ADDR sp, int struct_return, CORE_ADDR struct_addr);
extern CORE_ADDR gdbarch_push_dummy_call (struct gdbarch *gdbarch, struct value *function, struct regcache *regcache, CORE_ADDR bp_addr, int nargs, struct value **args, CORE_ADDR sp, int struct_return, CORE_ADDR struct_addr);
extern void set_gdbarch_push_dummy_call (struct gdbarch *gdbarch, gdbarch_push_dummy_call_ftype *push_dummy_call);

/* DEPRECATED_REGISTER_SIZE can be deleted. */

extern int gdbarch_deprecated_register_size (struct gdbarch *gdbarch);
extern void set_gdbarch_deprecated_register_size (struct gdbarch *gdbarch, int deprecated_register_size);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_REGISTER_SIZE)
#error "Non multi-arch definition of DEPRECATED_REGISTER_SIZE"
#endif
#if !defined (DEPRECATED_REGISTER_SIZE)
#define DEPRECATED_REGISTER_SIZE (gdbarch_deprecated_register_size (current_gdbarch))
#endif

extern int gdbarch_call_dummy_location (struct gdbarch *gdbarch);
extern void set_gdbarch_call_dummy_location (struct gdbarch *gdbarch, int call_dummy_location);
#if !defined (GDB_TM_FILE) && defined (CALL_DUMMY_LOCATION)
#error "Non multi-arch definition of CALL_DUMMY_LOCATION"
#endif
#if !defined (CALL_DUMMY_LOCATION)
#define CALL_DUMMY_LOCATION (gdbarch_call_dummy_location (current_gdbarch))
#endif

extern int gdbarch_push_dummy_code_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_push_dummy_code_ftype) (struct gdbarch *gdbarch, CORE_ADDR sp, CORE_ADDR funaddr, struct value **args, int nargs, struct type *value_type, CORE_ADDR *real_pc, CORE_ADDR *bp_addr);
extern CORE_ADDR gdbarch_push_dummy_code (struct gdbarch *gdbarch, CORE_ADDR sp, CORE_ADDR funaddr, struct value **args, int nargs, struct type *value_type, CORE_ADDR *real_pc, CORE_ADDR *bp_addr);
extern void set_gdbarch_push_dummy_code (struct gdbarch *gdbarch, gdbarch_push_dummy_code_ftype *push_dummy_code);

typedef void (gdbarch_print_registers_info_ftype) (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, int regnum, int all);
extern void gdbarch_print_registers_info (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, int regnum, int all);
extern void set_gdbarch_print_registers_info (struct gdbarch *gdbarch, gdbarch_print_registers_info_ftype *print_registers_info);

extern int gdbarch_print_float_info_p (struct gdbarch *gdbarch);

typedef void (gdbarch_print_float_info_ftype) (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, const char *args);
extern void gdbarch_print_float_info (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, const char *args);
extern void set_gdbarch_print_float_info (struct gdbarch *gdbarch, gdbarch_print_float_info_ftype *print_float_info);

extern int gdbarch_print_vector_info_p (struct gdbarch *gdbarch);

typedef void (gdbarch_print_vector_info_ftype) (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, const char *args);
extern void gdbarch_print_vector_info (struct gdbarch *gdbarch, struct ui_file *file, struct frame_info *frame, const char *args);
extern void set_gdbarch_print_vector_info (struct gdbarch *gdbarch, gdbarch_print_vector_info_ftype *print_vector_info);

/* MAP a GDB RAW register number onto a simulator register number.  See
   also include/...-sim.h. */

typedef int (gdbarch_register_sim_regno_ftype) (int reg_nr);
extern int gdbarch_register_sim_regno (struct gdbarch *gdbarch, int reg_nr);
extern void set_gdbarch_register_sim_regno (struct gdbarch *gdbarch, gdbarch_register_sim_regno_ftype *register_sim_regno);
#if !defined (GDB_TM_FILE) && defined (REGISTER_SIM_REGNO)
#error "Non multi-arch definition of REGISTER_SIM_REGNO"
#endif
#if !defined (REGISTER_SIM_REGNO)
#define REGISTER_SIM_REGNO(reg_nr) (gdbarch_register_sim_regno (current_gdbarch, reg_nr))
#endif

#if defined (REGISTER_BYTES_OK)
/* Legacy for systems yet to multi-arch REGISTER_BYTES_OK */
#if !defined (REGISTER_BYTES_OK_P)
#define REGISTER_BYTES_OK_P() (1)
#endif
#endif

extern int gdbarch_register_bytes_ok_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (REGISTER_BYTES_OK_P)
#error "Non multi-arch definition of REGISTER_BYTES_OK"
#endif
#if !defined (REGISTER_BYTES_OK_P)
#define REGISTER_BYTES_OK_P() (gdbarch_register_bytes_ok_p (current_gdbarch))
#endif

typedef int (gdbarch_register_bytes_ok_ftype) (long nr_bytes);
extern int gdbarch_register_bytes_ok (struct gdbarch *gdbarch, long nr_bytes);
extern void set_gdbarch_register_bytes_ok (struct gdbarch *gdbarch, gdbarch_register_bytes_ok_ftype *register_bytes_ok);
#if !defined (GDB_TM_FILE) && defined (REGISTER_BYTES_OK)
#error "Non multi-arch definition of REGISTER_BYTES_OK"
#endif
#if !defined (REGISTER_BYTES_OK)
#define REGISTER_BYTES_OK(nr_bytes) (gdbarch_register_bytes_ok (current_gdbarch, nr_bytes))
#endif

typedef int (gdbarch_cannot_fetch_register_ftype) (int regnum);
extern int gdbarch_cannot_fetch_register (struct gdbarch *gdbarch, int regnum);
extern void set_gdbarch_cannot_fetch_register (struct gdbarch *gdbarch, gdbarch_cannot_fetch_register_ftype *cannot_fetch_register);
#if !defined (GDB_TM_FILE) && defined (CANNOT_FETCH_REGISTER)
#error "Non multi-arch definition of CANNOT_FETCH_REGISTER"
#endif
#if !defined (CANNOT_FETCH_REGISTER)
#define CANNOT_FETCH_REGISTER(regnum) (gdbarch_cannot_fetch_register (current_gdbarch, regnum))
#endif

typedef int (gdbarch_cannot_store_register_ftype) (int regnum);
extern int gdbarch_cannot_store_register (struct gdbarch *gdbarch, int regnum);
extern void set_gdbarch_cannot_store_register (struct gdbarch *gdbarch, gdbarch_cannot_store_register_ftype *cannot_store_register);
#if !defined (GDB_TM_FILE) && defined (CANNOT_STORE_REGISTER)
#error "Non multi-arch definition of CANNOT_STORE_REGISTER"
#endif
#if !defined (CANNOT_STORE_REGISTER)
#define CANNOT_STORE_REGISTER(regnum) (gdbarch_cannot_store_register (current_gdbarch, regnum))
#endif

/* setjmp/longjmp support. */

#if defined (GET_LONGJMP_TARGET)
/* Legacy for systems yet to multi-arch GET_LONGJMP_TARGET */
#if !defined (GET_LONGJMP_TARGET_P)
#define GET_LONGJMP_TARGET_P() (1)
#endif
#endif

extern int gdbarch_get_longjmp_target_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (GET_LONGJMP_TARGET_P)
#error "Non multi-arch definition of GET_LONGJMP_TARGET"
#endif
#if !defined (GET_LONGJMP_TARGET_P)
#define GET_LONGJMP_TARGET_P() (gdbarch_get_longjmp_target_p (current_gdbarch))
#endif

typedef int (gdbarch_get_longjmp_target_ftype) (CORE_ADDR *pc);
extern int gdbarch_get_longjmp_target (struct gdbarch *gdbarch, CORE_ADDR *pc);
extern void set_gdbarch_get_longjmp_target (struct gdbarch *gdbarch, gdbarch_get_longjmp_target_ftype *get_longjmp_target);
#if !defined (GDB_TM_FILE) && defined (GET_LONGJMP_TARGET)
#error "Non multi-arch definition of GET_LONGJMP_TARGET"
#endif
#if !defined (GET_LONGJMP_TARGET)
#define GET_LONGJMP_TARGET(pc) (gdbarch_get_longjmp_target (current_gdbarch, pc))
#endif

extern int gdbarch_believe_pcc_promotion (struct gdbarch *gdbarch);
extern void set_gdbarch_believe_pcc_promotion (struct gdbarch *gdbarch, int believe_pcc_promotion);
#if !defined (GDB_TM_FILE) && defined (BELIEVE_PCC_PROMOTION)
#error "Non multi-arch definition of BELIEVE_PCC_PROMOTION"
#endif
#if !defined (BELIEVE_PCC_PROMOTION)
#define BELIEVE_PCC_PROMOTION (gdbarch_believe_pcc_promotion (current_gdbarch))
#endif

typedef int (gdbarch_convert_register_p_ftype) (int regnum, struct type *type);
extern int gdbarch_convert_register_p (struct gdbarch *gdbarch, int regnum, struct type *type);
extern void set_gdbarch_convert_register_p (struct gdbarch *gdbarch, gdbarch_convert_register_p_ftype *convert_register_p);
#if !defined (GDB_TM_FILE) && defined (CONVERT_REGISTER_P)
#error "Non multi-arch definition of CONVERT_REGISTER_P"
#endif
#if !defined (CONVERT_REGISTER_P)
#define CONVERT_REGISTER_P(regnum, type) (gdbarch_convert_register_p (current_gdbarch, regnum, type))
#endif

typedef void (gdbarch_register_to_value_ftype) (struct frame_info *frame, int regnum, struct type *type, gdb_byte *buf);
extern void gdbarch_register_to_value (struct gdbarch *gdbarch, struct frame_info *frame, int regnum, struct type *type, gdb_byte *buf);
extern void set_gdbarch_register_to_value (struct gdbarch *gdbarch, gdbarch_register_to_value_ftype *register_to_value);
#if !defined (GDB_TM_FILE) && defined (REGISTER_TO_VALUE)
#error "Non multi-arch definition of REGISTER_TO_VALUE"
#endif
#if !defined (REGISTER_TO_VALUE)
#define REGISTER_TO_VALUE(frame, regnum, type, buf) (gdbarch_register_to_value (current_gdbarch, frame, regnum, type, buf))
#endif

typedef void (gdbarch_value_to_register_ftype) (struct frame_info *frame, int regnum, struct type *type, const gdb_byte *buf);
extern void gdbarch_value_to_register (struct gdbarch *gdbarch, struct frame_info *frame, int regnum, struct type *type, const gdb_byte *buf);
extern void set_gdbarch_value_to_register (struct gdbarch *gdbarch, gdbarch_value_to_register_ftype *value_to_register);
#if !defined (GDB_TM_FILE) && defined (VALUE_TO_REGISTER)
#error "Non multi-arch definition of VALUE_TO_REGISTER"
#endif
#if !defined (VALUE_TO_REGISTER)
#define VALUE_TO_REGISTER(frame, regnum, type, buf) (gdbarch_value_to_register (current_gdbarch, frame, regnum, type, buf))
#endif

typedef CORE_ADDR (gdbarch_pointer_to_address_ftype) (struct type *type, const gdb_byte *buf);
extern CORE_ADDR gdbarch_pointer_to_address (struct gdbarch *gdbarch, struct type *type, const gdb_byte *buf);
extern void set_gdbarch_pointer_to_address (struct gdbarch *gdbarch, gdbarch_pointer_to_address_ftype *pointer_to_address);
#if !defined (GDB_TM_FILE) && defined (POINTER_TO_ADDRESS)
#error "Non multi-arch definition of POINTER_TO_ADDRESS"
#endif
#if !defined (POINTER_TO_ADDRESS)
#define POINTER_TO_ADDRESS(type, buf) (gdbarch_pointer_to_address (current_gdbarch, type, buf))
#endif

typedef void (gdbarch_address_to_pointer_ftype) (struct type *type, gdb_byte *buf, CORE_ADDR addr);
extern void gdbarch_address_to_pointer (struct gdbarch *gdbarch, struct type *type, gdb_byte *buf, CORE_ADDR addr);
extern void set_gdbarch_address_to_pointer (struct gdbarch *gdbarch, gdbarch_address_to_pointer_ftype *address_to_pointer);
#if !defined (GDB_TM_FILE) && defined (ADDRESS_TO_POINTER)
#error "Non multi-arch definition of ADDRESS_TO_POINTER"
#endif
#if !defined (ADDRESS_TO_POINTER)
#define ADDRESS_TO_POINTER(type, buf, addr) (gdbarch_address_to_pointer (current_gdbarch, type, buf, addr))
#endif

extern int gdbarch_integer_to_address_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_integer_to_address_ftype) (struct gdbarch *gdbarch, struct type *type, const gdb_byte *buf);
extern CORE_ADDR gdbarch_integer_to_address (struct gdbarch *gdbarch, struct type *type, const gdb_byte *buf);
extern void set_gdbarch_integer_to_address (struct gdbarch *gdbarch, gdbarch_integer_to_address_ftype *integer_to_address);

/* It has been suggested that this, well actually its predecessor,
   should take the type/value of the function to be called and not the
   return type.  This is left as an exercise for the reader. */

extern int gdbarch_return_value_p (struct gdbarch *gdbarch);

typedef enum return_value_convention (gdbarch_return_value_ftype) (struct gdbarch *gdbarch, struct type *functype, struct type *valtype, struct regcache *regcache, gdb_byte *readbuf, const gdb_byte *writebuf);
extern enum return_value_convention gdbarch_return_value (struct gdbarch *gdbarch, struct type *functype, struct type *valtype, struct regcache *regcache, gdb_byte *readbuf, const gdb_byte *writebuf);
extern void set_gdbarch_return_value (struct gdbarch *gdbarch, gdbarch_return_value_ftype *return_value);

typedef CORE_ADDR (gdbarch_skip_prologue_ftype) (CORE_ADDR ip);
extern CORE_ADDR gdbarch_skip_prologue (struct gdbarch *gdbarch, CORE_ADDR ip);
extern void set_gdbarch_skip_prologue (struct gdbarch *gdbarch, gdbarch_skip_prologue_ftype *skip_prologue);
#if !defined (GDB_TM_FILE) && defined (SKIP_PROLOGUE)
#error "Non multi-arch definition of SKIP_PROLOGUE"
#endif
#if !defined (SKIP_PROLOGUE)
#define SKIP_PROLOGUE(ip) (gdbarch_skip_prologue (current_gdbarch, ip))
#endif

#if defined (SKIP_PROLOGUE_ADDR_CTX)
/* Legacy for systems yet to multi-arch SKIP_PROLOGUE_ADDR_CTX */
#if !defined (SKIP_PROLOGUE_ADDR_CTX_P)
#define SKIP_PROLOGUE_ADDR_CTX_P() (1)
#endif
#endif

extern int gdbarch_skip_prologue_addr_ctx_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (SKIP_PROLOGUE_ADDR_CTX_P)
#error "Non multi-arch definition of SKIP_PROLOGUE_ADDR_CTX"
#endif
#if !defined (SKIP_PROLOGUE_ADDR_CTX_P)
#define SKIP_PROLOGUE_ADDR_CTX_P() (gdbarch_skip_prologue_addr_ctx_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_skip_prologue_addr_ctx_ftype) (struct address_context *addr_ctx);
extern CORE_ADDR gdbarch_skip_prologue_addr_ctx (struct gdbarch *gdbarch, struct address_context *addr_ctx);
extern void set_gdbarch_skip_prologue_addr_ctx (struct gdbarch *gdbarch, gdbarch_skip_prologue_addr_ctx_ftype *skip_prologue_addr_ctx);
#if !defined (GDB_TM_FILE) && defined (SKIP_PROLOGUE_ADDR_CTX)
#error "Non multi-arch definition of SKIP_PROLOGUE_ADDR_CTX"
#endif
#if !defined (SKIP_PROLOGUE_ADDR_CTX)
#define SKIP_PROLOGUE_ADDR_CTX(addr_ctx) (gdbarch_skip_prologue_addr_ctx (current_gdbarch, addr_ctx))
#endif

typedef int (gdbarch_inner_than_ftype) (CORE_ADDR lhs, CORE_ADDR rhs);
extern int gdbarch_inner_than (struct gdbarch *gdbarch, CORE_ADDR lhs, CORE_ADDR rhs);
extern void set_gdbarch_inner_than (struct gdbarch *gdbarch, gdbarch_inner_than_ftype *inner_than);
#if !defined (GDB_TM_FILE) && defined (INNER_THAN)
#error "Non multi-arch definition of INNER_THAN"
#endif
#if !defined (INNER_THAN)
#define INNER_THAN(lhs, rhs) (gdbarch_inner_than (current_gdbarch, lhs, rhs))
#endif

typedef const gdb_byte * (gdbarch_breakpoint_from_pc_ftype) (CORE_ADDR *pcptr, int *lenptr);
extern const gdb_byte * gdbarch_breakpoint_from_pc (struct gdbarch *gdbarch, CORE_ADDR *pcptr, int *lenptr);
extern void set_gdbarch_breakpoint_from_pc (struct gdbarch *gdbarch, gdbarch_breakpoint_from_pc_ftype *breakpoint_from_pc);
#if !defined (GDB_TM_FILE) && defined (BREAKPOINT_FROM_PC)
#error "Non multi-arch definition of BREAKPOINT_FROM_PC"
#endif
#if !defined (BREAKPOINT_FROM_PC)
#define BREAKPOINT_FROM_PC(pcptr, lenptr) (gdbarch_breakpoint_from_pc (current_gdbarch, pcptr, lenptr))
#endif

extern int gdbarch_adjust_breakpoint_address_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_adjust_breakpoint_address_ftype) (struct gdbarch *gdbarch, CORE_ADDR bpaddr);
extern CORE_ADDR gdbarch_adjust_breakpoint_address (struct gdbarch *gdbarch, CORE_ADDR bpaddr);
extern void set_gdbarch_adjust_breakpoint_address (struct gdbarch *gdbarch, gdbarch_adjust_breakpoint_address_ftype *adjust_breakpoint_address);

typedef int (gdbarch_memory_insert_breakpoint_ftype) (CORE_ADDR addr, gdb_byte *contents_cache);
extern int gdbarch_memory_insert_breakpoint (struct gdbarch *gdbarch, CORE_ADDR addr, gdb_byte *contents_cache);
extern void set_gdbarch_memory_insert_breakpoint (struct gdbarch *gdbarch, gdbarch_memory_insert_breakpoint_ftype *memory_insert_breakpoint);
#if !defined (GDB_TM_FILE) && defined (MEMORY_INSERT_BREAKPOINT)
#error "Non multi-arch definition of MEMORY_INSERT_BREAKPOINT"
#endif
#if !defined (MEMORY_INSERT_BREAKPOINT)
#define MEMORY_INSERT_BREAKPOINT(addr, contents_cache) (gdbarch_memory_insert_breakpoint (current_gdbarch, addr, contents_cache))
#endif

typedef int (gdbarch_memory_remove_breakpoint_ftype) (CORE_ADDR addr, gdb_byte *contents_cache);
extern int gdbarch_memory_remove_breakpoint (struct gdbarch *gdbarch, CORE_ADDR addr, gdb_byte *contents_cache);
extern void set_gdbarch_memory_remove_breakpoint (struct gdbarch *gdbarch, gdbarch_memory_remove_breakpoint_ftype *memory_remove_breakpoint);
#if !defined (GDB_TM_FILE) && defined (MEMORY_REMOVE_BREAKPOINT)
#error "Non multi-arch definition of MEMORY_REMOVE_BREAKPOINT"
#endif
#if !defined (MEMORY_REMOVE_BREAKPOINT)
#define MEMORY_REMOVE_BREAKPOINT(addr, contents_cache) (gdbarch_memory_remove_breakpoint (current_gdbarch, addr, contents_cache))
#endif

extern CORE_ADDR gdbarch_decr_pc_after_break (struct gdbarch *gdbarch);
extern void set_gdbarch_decr_pc_after_break (struct gdbarch *gdbarch, CORE_ADDR decr_pc_after_break);
#if !defined (GDB_TM_FILE) && defined (DECR_PC_AFTER_BREAK)
#error "Non multi-arch definition of DECR_PC_AFTER_BREAK"
#endif
#if !defined (DECR_PC_AFTER_BREAK)
#define DECR_PC_AFTER_BREAK (gdbarch_decr_pc_after_break (current_gdbarch))
#endif

/* A function can be addressed by either it's "pointer" (possibly a
   descriptor address) or "entry point" (first executable instruction).
   The method "convert_from_func_ptr_addr" converting the former to the
   latter.  DEPRECATED_FUNCTION_START_OFFSET is being used to implement
   a simplified subset of that functionality - the function's address
   corresponds to the "function pointer" and the function's start
   corresponds to the "function entry point" - and hence is redundant. */

extern CORE_ADDR gdbarch_deprecated_function_start_offset (struct gdbarch *gdbarch);
extern void set_gdbarch_deprecated_function_start_offset (struct gdbarch *gdbarch, CORE_ADDR deprecated_function_start_offset);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_FUNCTION_START_OFFSET)
#error "Non multi-arch definition of DEPRECATED_FUNCTION_START_OFFSET"
#endif
#if !defined (DEPRECATED_FUNCTION_START_OFFSET)
#define DEPRECATED_FUNCTION_START_OFFSET (gdbarch_deprecated_function_start_offset (current_gdbarch))
#endif

typedef void (gdbarch_remote_translate_xfer_address_ftype) (struct gdbarch *gdbarch, struct regcache *regcache, CORE_ADDR gdb_addr, int gdb_len, CORE_ADDR *rem_addr, int *rem_len);
extern void gdbarch_remote_translate_xfer_address (struct gdbarch *gdbarch, struct regcache *regcache, CORE_ADDR gdb_addr, int gdb_len, CORE_ADDR *rem_addr, int *rem_len);
extern void set_gdbarch_remote_translate_xfer_address (struct gdbarch *gdbarch, gdbarch_remote_translate_xfer_address_ftype *remote_translate_xfer_address);

/* Fetch the target specific address used to represent a load module. */

#if defined (FETCH_TLS_LOAD_MODULE_ADDRESS)
/* Legacy for systems yet to multi-arch FETCH_TLS_LOAD_MODULE_ADDRESS */
#if !defined (FETCH_TLS_LOAD_MODULE_ADDRESS_P)
#define FETCH_TLS_LOAD_MODULE_ADDRESS_P() (1)
#endif
#endif

extern int gdbarch_fetch_tls_load_module_address_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (FETCH_TLS_LOAD_MODULE_ADDRESS_P)
#error "Non multi-arch definition of FETCH_TLS_LOAD_MODULE_ADDRESS"
#endif
#if !defined (FETCH_TLS_LOAD_MODULE_ADDRESS_P)
#define FETCH_TLS_LOAD_MODULE_ADDRESS_P() (gdbarch_fetch_tls_load_module_address_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_fetch_tls_load_module_address_ftype) (struct objfile *objfile);
extern CORE_ADDR gdbarch_fetch_tls_load_module_address (struct gdbarch *gdbarch, struct objfile *objfile);
extern void set_gdbarch_fetch_tls_load_module_address (struct gdbarch *gdbarch, gdbarch_fetch_tls_load_module_address_ftype *fetch_tls_load_module_address);
#if !defined (GDB_TM_FILE) && defined (FETCH_TLS_LOAD_MODULE_ADDRESS)
#error "Non multi-arch definition of FETCH_TLS_LOAD_MODULE_ADDRESS"
#endif
#if !defined (FETCH_TLS_LOAD_MODULE_ADDRESS)
#define FETCH_TLS_LOAD_MODULE_ADDRESS(objfile) (gdbarch_fetch_tls_load_module_address (current_gdbarch, objfile))
#endif

extern CORE_ADDR gdbarch_frame_args_skip (struct gdbarch *gdbarch);
extern void set_gdbarch_frame_args_skip (struct gdbarch *gdbarch, CORE_ADDR frame_args_skip);
#if !defined (GDB_TM_FILE) && defined (FRAME_ARGS_SKIP)
#error "Non multi-arch definition of FRAME_ARGS_SKIP"
#endif
#if !defined (FRAME_ARGS_SKIP)
#define FRAME_ARGS_SKIP (gdbarch_frame_args_skip (current_gdbarch))
#endif

extern int gdbarch_unwind_pc_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_unwind_pc_ftype) (struct gdbarch *gdbarch, struct frame_info *next_frame);
extern CORE_ADDR gdbarch_unwind_pc (struct gdbarch *gdbarch, struct frame_info *next_frame);
extern void set_gdbarch_unwind_pc (struct gdbarch *gdbarch, gdbarch_unwind_pc_ftype *unwind_pc);

extern int gdbarch_unwind_sp_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_unwind_sp_ftype) (struct gdbarch *gdbarch, struct frame_info *next_frame);
extern CORE_ADDR gdbarch_unwind_sp (struct gdbarch *gdbarch, struct frame_info *next_frame);
extern void set_gdbarch_unwind_sp (struct gdbarch *gdbarch, gdbarch_unwind_sp_ftype *unwind_sp);

/* DEPRECATED_FRAME_LOCALS_ADDRESS as been replaced by the per-frame
   frame-base.  Enable frame-base before frame-unwind. */

#if defined (DEPRECATED_SAVED_PC_AFTER_CALL)
/* Legacy for systems yet to multi-arch DEPRECATED_SAVED_PC_AFTER_CALL */
#if !defined (DEPRECATED_SAVED_PC_AFTER_CALL_P)
#define DEPRECATED_SAVED_PC_AFTER_CALL_P() (1)
#endif
#endif

extern int gdbarch_deprecated_saved_pc_after_call_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_SAVED_PC_AFTER_CALL_P)
#error "Non multi-arch definition of DEPRECATED_SAVED_PC_AFTER_CALL"
#endif
#if !defined (DEPRECATED_SAVED_PC_AFTER_CALL_P)
#define DEPRECATED_SAVED_PC_AFTER_CALL_P() (gdbarch_deprecated_saved_pc_after_call_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_deprecated_saved_pc_after_call_ftype) (struct frame_info *frame);
extern CORE_ADDR gdbarch_deprecated_saved_pc_after_call (struct gdbarch *gdbarch, struct frame_info *frame);
extern void set_gdbarch_deprecated_saved_pc_after_call (struct gdbarch *gdbarch, gdbarch_deprecated_saved_pc_after_call_ftype *deprecated_saved_pc_after_call);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_SAVED_PC_AFTER_CALL)
#error "Non multi-arch definition of DEPRECATED_SAVED_PC_AFTER_CALL"
#endif
#if !defined (DEPRECATED_SAVED_PC_AFTER_CALL)
#define DEPRECATED_SAVED_PC_AFTER_CALL(frame) (gdbarch_deprecated_saved_pc_after_call (current_gdbarch, frame))
#endif

#if defined (FRAME_NUM_ARGS)
/* Legacy for systems yet to multi-arch FRAME_NUM_ARGS */
#if !defined (FRAME_NUM_ARGS_P)
#define FRAME_NUM_ARGS_P() (1)
#endif
#endif

extern int gdbarch_frame_num_args_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (FRAME_NUM_ARGS_P)
#error "Non multi-arch definition of FRAME_NUM_ARGS"
#endif
#if !defined (FRAME_NUM_ARGS_P)
#define FRAME_NUM_ARGS_P() (gdbarch_frame_num_args_p (current_gdbarch))
#endif

typedef int (gdbarch_frame_num_args_ftype) (struct frame_info *frame);
extern int gdbarch_frame_num_args (struct gdbarch *gdbarch, struct frame_info *frame);
extern void set_gdbarch_frame_num_args (struct gdbarch *gdbarch, gdbarch_frame_num_args_ftype *frame_num_args);
#if !defined (GDB_TM_FILE) && defined (FRAME_NUM_ARGS)
#error "Non multi-arch definition of FRAME_NUM_ARGS"
#endif
#if !defined (FRAME_NUM_ARGS)
#define FRAME_NUM_ARGS(frame) (gdbarch_frame_num_args (current_gdbarch, frame))
#endif

/* DEPRECATED_STACK_ALIGN has been replaced by an initial aligning call
   to frame_align and the requirement that methods such as
   push_dummy_call and frame_red_zone_size maintain correct stack/frame
   alignment. */

#if defined (DEPRECATED_STACK_ALIGN)
/* Legacy for systems yet to multi-arch DEPRECATED_STACK_ALIGN */
#if !defined (DEPRECATED_STACK_ALIGN_P)
#define DEPRECATED_STACK_ALIGN_P() (1)
#endif
#endif

extern int gdbarch_deprecated_stack_align_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_STACK_ALIGN_P)
#error "Non multi-arch definition of DEPRECATED_STACK_ALIGN"
#endif
#if !defined (DEPRECATED_STACK_ALIGN_P)
#define DEPRECATED_STACK_ALIGN_P() (gdbarch_deprecated_stack_align_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_deprecated_stack_align_ftype) (CORE_ADDR sp);
extern CORE_ADDR gdbarch_deprecated_stack_align (struct gdbarch *gdbarch, CORE_ADDR sp);
extern void set_gdbarch_deprecated_stack_align (struct gdbarch *gdbarch, gdbarch_deprecated_stack_align_ftype *deprecated_stack_align);
#if !defined (GDB_TM_FILE) && defined (DEPRECATED_STACK_ALIGN)
#error "Non multi-arch definition of DEPRECATED_STACK_ALIGN"
#endif
#if !defined (DEPRECATED_STACK_ALIGN)
#define DEPRECATED_STACK_ALIGN(sp) (gdbarch_deprecated_stack_align (current_gdbarch, sp))
#endif

extern int gdbarch_frame_align_p (struct gdbarch *gdbarch);

typedef CORE_ADDR (gdbarch_frame_align_ftype) (struct gdbarch *gdbarch, CORE_ADDR address);
extern CORE_ADDR gdbarch_frame_align (struct gdbarch *gdbarch, CORE_ADDR address);
extern void set_gdbarch_frame_align (struct gdbarch *gdbarch, gdbarch_frame_align_ftype *frame_align);

/* deprecated_reg_struct_has_addr has been replaced by
   stabs_argument_has_addr. */

extern int gdbarch_deprecated_reg_struct_has_addr_p (struct gdbarch *gdbarch);

typedef int (gdbarch_deprecated_reg_struct_has_addr_ftype) (int gcc_p, struct type *type);
extern int gdbarch_deprecated_reg_struct_has_addr (struct gdbarch *gdbarch, int gcc_p, struct type *type);
extern void set_gdbarch_deprecated_reg_struct_has_addr (struct gdbarch *gdbarch, gdbarch_deprecated_reg_struct_has_addr_ftype *deprecated_reg_struct_has_addr);

typedef int (gdbarch_stabs_argument_has_addr_ftype) (struct gdbarch *gdbarch, struct type *type);
extern int gdbarch_stabs_argument_has_addr (struct gdbarch *gdbarch, struct type *type);
extern void set_gdbarch_stabs_argument_has_addr (struct gdbarch *gdbarch, gdbarch_stabs_argument_has_addr_ftype *stabs_argument_has_addr);

extern int gdbarch_frame_red_zone_size (struct gdbarch *gdbarch);
extern void set_gdbarch_frame_red_zone_size (struct gdbarch *gdbarch, int frame_red_zone_size);
#if !defined (GDB_TM_FILE) && defined (FRAME_RED_ZONE_SIZE)
#error "Non multi-arch definition of FRAME_RED_ZONE_SIZE"
#endif
#if !defined (FRAME_RED_ZONE_SIZE)
#define FRAME_RED_ZONE_SIZE (gdbarch_frame_red_zone_size (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_convert_from_func_ptr_addr_ftype) (struct gdbarch *gdbarch, CORE_ADDR addr, struct target_ops *targ);
extern CORE_ADDR gdbarch_convert_from_func_ptr_addr (struct gdbarch *gdbarch, CORE_ADDR addr, struct target_ops *targ);
extern void set_gdbarch_convert_from_func_ptr_addr (struct gdbarch *gdbarch, gdbarch_convert_from_func_ptr_addr_ftype *convert_from_func_ptr_addr);

/* On some machines there are bits in addresses which are not really
   part of the address, but are used by the kernel, the hardware, etc.
   for special purposes.  ADDR_BITS_REMOVE takes out any such bits so
   we get a "real" address such as one would find in a symbol table.
   This is used only for addresses of instructions, and even then I'm
   not sure it's used in all contexts.  It exists to deal with there
   being a few stray bits in the PC which would mislead us, not as some
   sort of generic thing to handle alignment or segmentation (it's
   possible it should be in TARGET_READ_PC instead). */

typedef CORE_ADDR (gdbarch_addr_bits_remove_ftype) (CORE_ADDR addr);
extern CORE_ADDR gdbarch_addr_bits_remove (struct gdbarch *gdbarch, CORE_ADDR addr);
extern void set_gdbarch_addr_bits_remove (struct gdbarch *gdbarch, gdbarch_addr_bits_remove_ftype *addr_bits_remove);
#if !defined (GDB_TM_FILE) && defined (ADDR_BITS_REMOVE)
#error "Non multi-arch definition of ADDR_BITS_REMOVE"
#endif
#if !defined (ADDR_BITS_REMOVE)
#define ADDR_BITS_REMOVE(addr) (gdbarch_addr_bits_remove (current_gdbarch, addr))
#endif

/* It is not at all clear why SMASH_TEXT_ADDRESS is not folded into
   ADDR_BITS_REMOVE. */

typedef CORE_ADDR (gdbarch_smash_text_address_ftype) (CORE_ADDR addr);
extern CORE_ADDR gdbarch_smash_text_address (struct gdbarch *gdbarch, CORE_ADDR addr);
extern void set_gdbarch_smash_text_address (struct gdbarch *gdbarch, gdbarch_smash_text_address_ftype *smash_text_address);
#if !defined (GDB_TM_FILE) && defined (SMASH_TEXT_ADDRESS)
#error "Non multi-arch definition of SMASH_TEXT_ADDRESS"
#endif
#if !defined (SMASH_TEXT_ADDRESS)
#define SMASH_TEXT_ADDRESS(addr) (gdbarch_smash_text_address (current_gdbarch, addr))
#endif

/* FIXME/cagney/2001-01-18: This should be split in two.  A target method that indicates if
   the target needs software single step.  An ISA method to implement it.
  
   FIXME/cagney/2001-01-18: This should be replaced with something that inserts breakpoints
   using the breakpoint system instead of blatting memory directly (as with rs6000).
  
   FIXME/cagney/2001-01-18: The logic is backwards.  It should be asking if the target can
   single step.  If not, then implement single step using breakpoints. */

#if defined (SOFTWARE_SINGLE_STEP)
/* Legacy for systems yet to multi-arch SOFTWARE_SINGLE_STEP */
#if !defined (SOFTWARE_SINGLE_STEP_P)
#define SOFTWARE_SINGLE_STEP_P() (1)
#endif
#endif

extern int gdbarch_software_single_step_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (SOFTWARE_SINGLE_STEP_P)
#error "Non multi-arch definition of SOFTWARE_SINGLE_STEP"
#endif
#if !defined (SOFTWARE_SINGLE_STEP_P)
#define SOFTWARE_SINGLE_STEP_P() (gdbarch_software_single_step_p (current_gdbarch))
#endif

typedef void (gdbarch_software_single_step_ftype) (enum target_signal sig, int insert_breakpoints_p);
extern void gdbarch_software_single_step (struct gdbarch *gdbarch, enum target_signal sig, int insert_breakpoints_p);
extern void set_gdbarch_software_single_step (struct gdbarch *gdbarch, gdbarch_software_single_step_ftype *software_single_step);
#if !defined (GDB_TM_FILE) && defined (SOFTWARE_SINGLE_STEP)
#error "Non multi-arch definition of SOFTWARE_SINGLE_STEP"
#endif
#if !defined (SOFTWARE_SINGLE_STEP)
#define SOFTWARE_SINGLE_STEP(sig, insert_breakpoints_p) (gdbarch_software_single_step (current_gdbarch, sig, insert_breakpoints_p))
#endif

/* Return non-zero if the processor is executing a delay slot and a
   further single-step is needed before the instruction finishes. */

extern int gdbarch_single_step_through_delay_p (struct gdbarch *gdbarch);

typedef int (gdbarch_single_step_through_delay_ftype) (struct gdbarch *gdbarch, struct frame_info *frame);
extern int gdbarch_single_step_through_delay (struct gdbarch *gdbarch, struct frame_info *frame);
extern void set_gdbarch_single_step_through_delay (struct gdbarch *gdbarch, gdbarch_single_step_through_delay_ftype *single_step_through_delay);

/* FIXME: cagney/2003-08-28: Need to find a better way of selecting the
   disassembler.  Perhaps objdump can handle it? */

typedef int (gdbarch_print_insn_ftype) (bfd_vma vma, struct disassemble_info *info);
extern int gdbarch_print_insn (struct gdbarch *gdbarch, bfd_vma vma, struct disassemble_info *info);
extern void set_gdbarch_print_insn (struct gdbarch *gdbarch, gdbarch_print_insn_ftype *print_insn);
#if !defined (GDB_TM_FILE) && defined (TARGET_PRINT_INSN)
#error "Non multi-arch definition of TARGET_PRINT_INSN"
#endif
#if !defined (TARGET_PRINT_INSN)
#define TARGET_PRINT_INSN(vma, info) (gdbarch_print_insn (current_gdbarch, vma, info))
#endif

typedef CORE_ADDR (gdbarch_skip_trampoline_code_ftype) (CORE_ADDR pc);
extern CORE_ADDR gdbarch_skip_trampoline_code (struct gdbarch *gdbarch, CORE_ADDR pc);
extern void set_gdbarch_skip_trampoline_code (struct gdbarch *gdbarch, gdbarch_skip_trampoline_code_ftype *skip_trampoline_code);
#if !defined (GDB_TM_FILE) && defined (SKIP_TRAMPOLINE_CODE)
#error "Non multi-arch definition of SKIP_TRAMPOLINE_CODE"
#endif
#if !defined (SKIP_TRAMPOLINE_CODE)
#define SKIP_TRAMPOLINE_CODE(pc) (gdbarch_skip_trampoline_code (current_gdbarch, pc))
#endif

/* If IN_SOLIB_DYNSYM_RESOLVE_CODE returns true, and SKIP_SOLIB_RESOLVER
   evaluates non-zero, this is the address where the debugger will place
   a step-resume breakpoint to get us past the dynamic linker. */

typedef CORE_ADDR (gdbarch_skip_solib_resolver_ftype) (struct gdbarch *gdbarch, CORE_ADDR pc);
extern CORE_ADDR gdbarch_skip_solib_resolver (struct gdbarch *gdbarch, CORE_ADDR pc);
extern void set_gdbarch_skip_solib_resolver (struct gdbarch *gdbarch, gdbarch_skip_solib_resolver_ftype *skip_solib_resolver);

/* Some systems also have trampoline code for returning from shared libs. */

typedef int (gdbarch_in_solib_return_trampoline_ftype) (CORE_ADDR pc, char *name);
extern int gdbarch_in_solib_return_trampoline (struct gdbarch *gdbarch, CORE_ADDR pc, char *name);
extern void set_gdbarch_in_solib_return_trampoline (struct gdbarch *gdbarch, gdbarch_in_solib_return_trampoline_ftype *in_solib_return_trampoline);
#if !defined (GDB_TM_FILE) && defined (IN_SOLIB_RETURN_TRAMPOLINE)
#error "Non multi-arch definition of IN_SOLIB_RETURN_TRAMPOLINE"
#endif
#if !defined (IN_SOLIB_RETURN_TRAMPOLINE)
#define IN_SOLIB_RETURN_TRAMPOLINE(pc, name) (gdbarch_in_solib_return_trampoline (current_gdbarch, pc, name))
#endif

/* A target might have problems with watchpoints as soon as the stack
   frame of the current function has been destroyed.  This mostly happens
   as the first action in a funtion's epilogue.  in_function_epilogue_p()
   is defined to return a non-zero value if either the given addr is one
   instruction after the stack destroying instruction up to the trailing
   return instruction or if we can figure out that the stack frame has
   already been invalidated regardless of the value of addr.  Targets
   which don't suffer from that problem could just let this functionality
   untouched. */

typedef int (gdbarch_in_function_epilogue_p_ftype) (struct gdbarch *gdbarch, CORE_ADDR addr);
extern int gdbarch_in_function_epilogue_p (struct gdbarch *gdbarch, CORE_ADDR addr);
extern void set_gdbarch_in_function_epilogue_p (struct gdbarch *gdbarch, gdbarch_in_function_epilogue_p_ftype *in_function_epilogue_p);

/* Given a vector of command-line arguments, return a newly allocated
   string which, when passed to the create_inferior function, will be
   parsed (on Unix systems, by the shell) to yield the same vector.
   This function should call error() if the argument vector is not
   representable for this target or if this target does not support
   command-line arguments.
   ARGC is the number of elements in the vector.
   ARGV is an array of strings, one per argument. */

typedef char * (gdbarch_construct_inferior_arguments_ftype) (struct gdbarch *gdbarch, int argc, char **argv);
extern char * gdbarch_construct_inferior_arguments (struct gdbarch *gdbarch, int argc, char **argv);
extern void set_gdbarch_construct_inferior_arguments (struct gdbarch *gdbarch, gdbarch_construct_inferior_arguments_ftype *construct_inferior_arguments);

typedef void (gdbarch_elf_make_msymbol_special_ftype) (asymbol *sym, struct minimal_symbol *msym);
extern void gdbarch_elf_make_msymbol_special (struct gdbarch *gdbarch, asymbol *sym, struct minimal_symbol *msym);
extern void set_gdbarch_elf_make_msymbol_special (struct gdbarch *gdbarch, gdbarch_elf_make_msymbol_special_ftype *elf_make_msymbol_special);
#if !defined (GDB_TM_FILE) && defined (ELF_MAKE_MSYMBOL_SPECIAL)
#error "Non multi-arch definition of ELF_MAKE_MSYMBOL_SPECIAL"
#endif
#if !defined (ELF_MAKE_MSYMBOL_SPECIAL)
#define ELF_MAKE_MSYMBOL_SPECIAL(sym, msym) (gdbarch_elf_make_msymbol_special (current_gdbarch, sym, msym))
#endif

typedef void (gdbarch_coff_make_msymbol_special_ftype) (int val, struct minimal_symbol *msym);
extern void gdbarch_coff_make_msymbol_special (struct gdbarch *gdbarch, int val, struct minimal_symbol *msym);
extern void set_gdbarch_coff_make_msymbol_special (struct gdbarch *gdbarch, gdbarch_coff_make_msymbol_special_ftype *coff_make_msymbol_special);
#if !defined (GDB_TM_FILE) && defined (COFF_MAKE_MSYMBOL_SPECIAL)
#error "Non multi-arch definition of COFF_MAKE_MSYMBOL_SPECIAL"
#endif
#if !defined (COFF_MAKE_MSYMBOL_SPECIAL)
#define COFF_MAKE_MSYMBOL_SPECIAL(val, msym) (gdbarch_coff_make_msymbol_special (current_gdbarch, val, msym))
#endif

/* APPLE LOCAL: The symbols are marked as thumb in the nlist entries, so we need this. */

typedef void (gdbarch_dbx_make_msymbol_special_ftype) (int16_t desc, struct minimal_symbol *msym);
extern void gdbarch_dbx_make_msymbol_special (struct gdbarch *gdbarch, int16_t desc, struct minimal_symbol *msym);
extern void set_gdbarch_dbx_make_msymbol_special (struct gdbarch *gdbarch, gdbarch_dbx_make_msymbol_special_ftype *dbx_make_msymbol_special);
#if !defined (GDB_TM_FILE) && defined (DBX_MAKE_MSYMBOL_SPECIAL)
#error "Non multi-arch definition of DBX_MAKE_MSYMBOL_SPECIAL"
#endif
#if !defined (DBX_MAKE_MSYMBOL_SPECIAL)
#define DBX_MAKE_MSYMBOL_SPECIAL(desc, msym) (gdbarch_dbx_make_msymbol_special (current_gdbarch, desc, msym))
#endif

extern const char * gdbarch_name_of_malloc (struct gdbarch *gdbarch);
extern void set_gdbarch_name_of_malloc (struct gdbarch *gdbarch, const char * name_of_malloc);
#if !defined (GDB_TM_FILE) && defined (NAME_OF_MALLOC)
#error "Non multi-arch definition of NAME_OF_MALLOC"
#endif
#if !defined (NAME_OF_MALLOC)
#define NAME_OF_MALLOC (gdbarch_name_of_malloc (current_gdbarch))
#endif

extern int gdbarch_cannot_step_breakpoint (struct gdbarch *gdbarch);
extern void set_gdbarch_cannot_step_breakpoint (struct gdbarch *gdbarch, int cannot_step_breakpoint);
#if !defined (GDB_TM_FILE) && defined (CANNOT_STEP_BREAKPOINT)
#error "Non multi-arch definition of CANNOT_STEP_BREAKPOINT"
#endif
#if !defined (CANNOT_STEP_BREAKPOINT)
#define CANNOT_STEP_BREAKPOINT (gdbarch_cannot_step_breakpoint (current_gdbarch))
#endif

extern int gdbarch_have_nonsteppable_watchpoint (struct gdbarch *gdbarch);
extern void set_gdbarch_have_nonsteppable_watchpoint (struct gdbarch *gdbarch, int have_nonsteppable_watchpoint);
#if !defined (GDB_TM_FILE) && defined (HAVE_NONSTEPPABLE_WATCHPOINT)
#error "Non multi-arch definition of HAVE_NONSTEPPABLE_WATCHPOINT"
#endif
#if !defined (HAVE_NONSTEPPABLE_WATCHPOINT)
#define HAVE_NONSTEPPABLE_WATCHPOINT (gdbarch_have_nonsteppable_watchpoint (current_gdbarch))
#endif

#if defined (ADDRESS_CLASS_TYPE_FLAGS)
/* Legacy for systems yet to multi-arch ADDRESS_CLASS_TYPE_FLAGS */
#if !defined (ADDRESS_CLASS_TYPE_FLAGS_P)
#define ADDRESS_CLASS_TYPE_FLAGS_P() (1)
#endif
#endif

extern int gdbarch_address_class_type_flags_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (ADDRESS_CLASS_TYPE_FLAGS_P)
#error "Non multi-arch definition of ADDRESS_CLASS_TYPE_FLAGS"
#endif
#if !defined (ADDRESS_CLASS_TYPE_FLAGS_P)
#define ADDRESS_CLASS_TYPE_FLAGS_P() (gdbarch_address_class_type_flags_p (current_gdbarch))
#endif

typedef int (gdbarch_address_class_type_flags_ftype) (int byte_size, int dwarf2_addr_class);
extern int gdbarch_address_class_type_flags (struct gdbarch *gdbarch, int byte_size, int dwarf2_addr_class);
extern void set_gdbarch_address_class_type_flags (struct gdbarch *gdbarch, gdbarch_address_class_type_flags_ftype *address_class_type_flags);
#if !defined (GDB_TM_FILE) && defined (ADDRESS_CLASS_TYPE_FLAGS)
#error "Non multi-arch definition of ADDRESS_CLASS_TYPE_FLAGS"
#endif
#if !defined (ADDRESS_CLASS_TYPE_FLAGS)
#define ADDRESS_CLASS_TYPE_FLAGS(byte_size, dwarf2_addr_class) (gdbarch_address_class_type_flags (current_gdbarch, byte_size, dwarf2_addr_class))
#endif

extern int gdbarch_address_class_type_flags_to_name_p (struct gdbarch *gdbarch);

typedef const char * (gdbarch_address_class_type_flags_to_name_ftype) (struct gdbarch *gdbarch, int type_flags);
extern const char * gdbarch_address_class_type_flags_to_name (struct gdbarch *gdbarch, int type_flags);
extern void set_gdbarch_address_class_type_flags_to_name (struct gdbarch *gdbarch, gdbarch_address_class_type_flags_to_name_ftype *address_class_type_flags_to_name);

extern int gdbarch_address_class_name_to_type_flags_p (struct gdbarch *gdbarch);

typedef int (gdbarch_address_class_name_to_type_flags_ftype) (struct gdbarch *gdbarch, const char *name, int *type_flags_ptr);
extern int gdbarch_address_class_name_to_type_flags (struct gdbarch *gdbarch, const char *name, int *type_flags_ptr);
extern void set_gdbarch_address_class_name_to_type_flags (struct gdbarch *gdbarch, gdbarch_address_class_name_to_type_flags_ftype *address_class_name_to_type_flags);

/* Is a register in a group */

typedef int (gdbarch_register_reggroup_p_ftype) (struct gdbarch *gdbarch, int regnum, struct reggroup *reggroup);
extern int gdbarch_register_reggroup_p (struct gdbarch *gdbarch, int regnum, struct reggroup *reggroup);
extern void set_gdbarch_register_reggroup_p (struct gdbarch *gdbarch, gdbarch_register_reggroup_p_ftype *register_reggroup_p);

/* Fetch the pointer to the ith function argument. */

#if defined (FETCH_POINTER_ARGUMENT)
/* Legacy for systems yet to multi-arch FETCH_POINTER_ARGUMENT */
#if !defined (FETCH_POINTER_ARGUMENT_P)
#define FETCH_POINTER_ARGUMENT_P() (1)
#endif
#endif

extern int gdbarch_fetch_pointer_argument_p (struct gdbarch *gdbarch);
#if !defined (GDB_TM_FILE) && defined (FETCH_POINTER_ARGUMENT_P)
#error "Non multi-arch definition of FETCH_POINTER_ARGUMENT"
#endif
#if !defined (FETCH_POINTER_ARGUMENT_P)
#define FETCH_POINTER_ARGUMENT_P() (gdbarch_fetch_pointer_argument_p (current_gdbarch))
#endif

typedef CORE_ADDR (gdbarch_fetch_pointer_argument_ftype) (struct frame_info *frame, int argi, struct type *type);
extern CORE_ADDR gdbarch_fetch_pointer_argument (struct gdbarch *gdbarch, struct frame_info *frame, int argi, struct type *type);
extern void set_gdbarch_fetch_pointer_argument (struct gdbarch *gdbarch, gdbarch_fetch_pointer_argument_ftype *fetch_pointer_argument);
#if !defined (GDB_TM_FILE) && defined (FETCH_POINTER_ARGUMENT)
#error "Non multi-arch definition of FETCH_POINTER_ARGUMENT"
#endif
#if !defined (FETCH_POINTER_ARGUMENT)
#define FETCH_POINTER_ARGUMENT(frame, argi, type) (gdbarch_fetch_pointer_argument (current_gdbarch, frame, argi, type))
#endif

/* Return the appropriate register set for a core file section with
   name SECT_NAME and size SECT_SIZE. */

extern int gdbarch_regset_from_core_section_p (struct gdbarch *gdbarch);

typedef const struct regset * (gdbarch_regset_from_core_section_ftype) (struct gdbarch *gdbarch, const char *sect_name, size_t sect_size);
extern const struct regset * gdbarch_regset_from_core_section (struct gdbarch *gdbarch, const char *sect_name, size_t sect_size);
extern void set_gdbarch_regset_from_core_section (struct gdbarch *gdbarch, gdbarch_regset_from_core_section_ftype *regset_from_core_section);

/* APPLE LOCAL: Translate eh frame regnums into dwarf regnums */

typedef int (gdbarch_adjust_ehframe_regnum_ftype) (struct gdbarch *gdbarch, int regnum, int eh_frame_p);
extern int gdbarch_adjust_ehframe_regnum (struct gdbarch *gdbarch, int regnum, int eh_frame_p);
extern void set_gdbarch_adjust_ehframe_regnum (struct gdbarch *gdbarch, gdbarch_adjust_ehframe_regnum_ftype *adjust_ehframe_regnum);

/* If the elements of C++ vtables are in-place function descriptors rather
   than normal function pointers (which may point to code or a descriptor),
   set this to one. */

extern int gdbarch_vtable_function_descriptors (struct gdbarch *gdbarch);
extern void set_gdbarch_vtable_function_descriptors (struct gdbarch *gdbarch, int vtable_function_descriptors);

/* Set if the least significant bit of the delta is used instead of the least
   significant bit of the pfn for pointers to virtual member functions. */

extern int gdbarch_vbit_in_delta (struct gdbarch *gdbarch);
extern void set_gdbarch_vbit_in_delta (struct gdbarch *gdbarch, int vbit_in_delta);

/* EMBARCADERO Local begin calling conventions */
typedef int (gdbarch_calling_convention_supported_ftype) (struct value *function);
extern int gdbarch_calling_convention_supported (struct gdbarch *gdbarch,
						 struct value *function);
extern void set_gdbarch_calling_convention_supported (struct gdbarch *gdbarch, gdbarch_calling_convention_supported_ftype *calling_convention_supported);

typedef const char *(gdbarch_calling_convention_string_ftype) (struct value *function);
extern const char *gdbarch_calling_convention_string (struct gdbarch *gdbarch, struct value *function);
extern void set_gdbarch_calling_convention_string (struct gdbarch *gdbarch, gdbarch_calling_convention_string_ftype *calling_convention_string);
/* EMBARCADERO Local end calling conventions */

extern struct gdbarch_tdep *gdbarch_tdep (struct gdbarch *gdbarch);


/* Mechanism for co-ordinating the selection of a specific
   architecture.

   GDB targets (*-tdep.c) can register an interest in a specific
   architecture.  Other GDB components can register a need to maintain
   per-architecture data.

   The mechanisms below ensures that there is only a loose connection
   between the set-architecture command and the various GDB
   components.  Each component can independently register their need
   to maintain architecture specific data with gdbarch.

   Pragmatics:

   Previously, a single TARGET_ARCHITECTURE_HOOK was provided.  It
   didn't scale.

   The more traditional mega-struct containing architecture specific
   data for all the various GDB components was also considered.  Since
   GDB is built from a variable number of (fairly independent)
   components it was determined that the global aproach was not
   applicable. */


/* Register a new architectural family with GDB.

   Register support for the specified ARCHITECTURE with GDB.  When
   gdbarch determines that the specified architecture has been
   selected, the corresponding INIT function is called.

   --

   The INIT function takes two parameters: INFO which contains the
   information available to gdbarch about the (possibly new)
   architecture; ARCHES which is a list of the previously created
   ``struct gdbarch'' for this architecture.

   The INFO parameter is, as far as possible, be pre-initialized with
   information obtained from INFO.ABFD or the previously selected
   architecture.

   The ARCHES parameter is a linked list (sorted most recently used)
   of all the previously created architures for this architecture
   family.  The (possibly NULL) ARCHES->gdbarch can used to access
   values from the previously selected architecture for this
   architecture family.  The global ``current_gdbarch'' shall not be
   used.

   The INIT function shall return any of: NULL - indicating that it
   doesn't recognize the selected architecture; an existing ``struct
   gdbarch'' from the ARCHES list - indicating that the new
   architecture is just a synonym for an earlier architecture (see
   gdbarch_list_lookup_by_info()); a newly created ``struct gdbarch''
   - that describes the selected architecture (see gdbarch_alloc()).

   The DUMP_TDEP function shall print out all target specific values.
   Care should be taken to ensure that the function works in both the
   multi-arch and non- multi-arch cases. */

struct gdbarch_list
{
  struct gdbarch *gdbarch;
  struct gdbarch_list *next;
};

struct gdbarch_info
{
  /* Use default: NULL (ZERO). */
  const struct bfd_arch_info *bfd_arch_info;

  /* Use default: BFD_ENDIAN_UNKNOWN (NB: is not ZERO).  */
  int byte_order;

  /* Use default: NULL (ZERO). */
  bfd *abfd;

  /* Use default: NULL (ZERO). */
  struct gdbarch_tdep_info *tdep_info;

  /* Use default: GDB_OSABI_UNINITIALIZED (-1).  */
  enum gdb_osabi osabi;
};

typedef struct gdbarch *(gdbarch_init_ftype) (struct gdbarch_info info, struct gdbarch_list *arches);
typedef void (gdbarch_dump_tdep_ftype) (struct gdbarch *gdbarch, struct ui_file *file);

/* DEPRECATED - use gdbarch_register() */
extern void register_gdbarch_init (enum bfd_architecture architecture, gdbarch_init_ftype *);

extern void gdbarch_register (enum bfd_architecture architecture,
                              gdbarch_init_ftype *,
                              gdbarch_dump_tdep_ftype *);


/* Return a freshly allocated, NULL terminated, array of the valid
   architecture names.  Since architectures are registered during the
   _initialize phase this function only returns useful information
   once initialization has been completed. */

extern const char **gdbarch_printable_names (void);


/* Helper function.  Search the list of ARCHES for a GDBARCH that
   matches the information provided by INFO. */

extern struct gdbarch_list *gdbarch_list_lookup_by_info (struct gdbarch_list *arches,  const struct gdbarch_info *info);


/* Helper function.  Create a preliminary ``struct gdbarch''.  Perform
   basic initialization using values obtained from the INFO andTDEP
   parameters.  set_gdbarch_*() functions are called to complete the
   initialization of the object. */

extern struct gdbarch *gdbarch_alloc (const struct gdbarch_info *info, struct gdbarch_tdep *tdep);


/* Helper function.  Free a partially-constructed ``struct gdbarch''.
   It is assumed that the caller freeds the ``struct
   gdbarch_tdep''. */

extern void gdbarch_free (struct gdbarch *);


/* Helper function.  Allocate memory from the ``struct gdbarch''
   obstack.  The memory is freed when the corresponding architecture
   is also freed.  */

extern void *gdbarch_obstack_zalloc (struct gdbarch *gdbarch, long size);
#define GDBARCH_OBSTACK_CALLOC(GDBARCH, NR, TYPE) ((TYPE *) gdbarch_obstack_zalloc ((GDBARCH), (NR) * sizeof (TYPE)))
#define GDBARCH_OBSTACK_ZALLOC(GDBARCH, TYPE) ((TYPE *) gdbarch_obstack_zalloc ((GDBARCH), sizeof (TYPE)))


/* Helper function. Force an update of the current architecture.

   The actual architecture selected is determined by INFO, ``(gdb) set
   architecture'' et.al., the existing architecture and BFD's default
   architecture.  INFO should be initialized to zero and then selected
   fields should be updated.

   Returns non-zero if the update succeeds */

extern int gdbarch_update_p (struct gdbarch_info info);


/* Helper function.  Find an architecture matching info.

   INFO should be initialized using gdbarch_info_init, relevant fields
   set, and then finished using gdbarch_info_fill.

   Returns the corresponding architecture, or NULL if no matching
   architecture was found.  "current_gdbarch" is not updated.  */

extern struct gdbarch *gdbarch_find_by_info (struct gdbarch_info info);


/* Helper function.  Set the global "current_gdbarch" to "gdbarch".

   FIXME: kettenis/20031124: Of the functions that follow, only
   gdbarch_from_bfd is supposed to survive.  The others will
   dissappear since in the future GDB will (hopefully) be truly
   multi-arch.  However, for now we're still stuck with the concept of
   a single active architecture.  */

extern void deprecated_current_gdbarch_select_hack (struct gdbarch *gdbarch);


/* Register per-architecture data-pointer.

   Reserve space for a per-architecture data-pointer.  An identifier
   for the reserved data-pointer is returned.  That identifer should
   be saved in a local static variable.

   Memory for the per-architecture data shall be allocated using
   gdbarch_obstack_zalloc.  That memory will be deleted when the
   corresponding architecture object is deleted.

   When a previously created architecture is re-selected, the
   per-architecture data-pointer for that previous architecture is
   restored.  INIT() is not re-called.

   Multiple registrarants for any architecture are allowed (and
   strongly encouraged).  */

struct gdbarch_data;

typedef void *(gdbarch_data_pre_init_ftype) (struct obstack *obstack);
extern struct gdbarch_data *gdbarch_data_register_pre_init (gdbarch_data_pre_init_ftype *init);
typedef void *(gdbarch_data_post_init_ftype) (struct gdbarch *gdbarch);
extern struct gdbarch_data *gdbarch_data_register_post_init (gdbarch_data_post_init_ftype *init);
extern void deprecated_set_gdbarch_data (struct gdbarch *gdbarch,
                                         struct gdbarch_data *data,
			                 void *pointer);

extern void *gdbarch_data (struct gdbarch *gdbarch, struct gdbarch_data *);



/* Register per-architecture memory region.

   Provide a memory-region swap mechanism.  Per-architecture memory
   region are created.  These memory regions are swapped whenever the
   architecture is changed.  For a new architecture, the memory region
   is initialized with zero (0) and the INIT function is called.

   Memory regions are swapped / initialized in the order that they are
   registered.  NULL DATA and/or INIT values can be specified.

   New code should use gdbarch_data_register_*(). */

typedef void (gdbarch_swap_ftype) (void);
extern void deprecated_register_gdbarch_swap (void *data, unsigned long size, gdbarch_swap_ftype *init);
#define DEPRECATED_REGISTER_GDBARCH_SWAP(VAR) deprecated_register_gdbarch_swap (&(VAR), sizeof ((VAR)), NULL)

/* Set the dynamic target-system-dependent parameters (architecture,
   byte-order, ...) using information found in the BFD */

extern void set_gdbarch_from_file (bfd *);


/* Initialize the current architecture to the "first" one we find on
   our list.  */

extern void initialize_current_architecture (void);

/* gdbarch trace variable */
extern int gdbarch_debug;

extern void gdbarch_dump (struct gdbarch *gdbarch, struct ui_file *file);

/* EMBARCADERO Local: fCall Wrapper function arguments pusher */
/* Function type, gdbarch API and setter for arch specific fCall Wrapper 
   arguments pusher.  */
typedef int (gdbarch_fcw_argument_push_ftype) (struct gdbarch *gdbarch);
extern int gdbarch_fcw_argument_push (struct gdbarch *gdbarch);
extern void set_gdbarch_fcw_argument_push (struct gdbarch *gdbarch,
					   gdbarch_fcw_argument_push_ftype *fcw_argument_push);

/* EMBARCADERO Local: Delphi ABI */
/* This is an alternate version of stabs_argument_has_addr (and
   gdbarch_deprecated_reg_struct_has_addr) which also
   tests the function type (not just the argument type). 
   Think of this as the pass-by-value version of gdbarch_return_value, in that
   it determines if an argument's value should be passed via reference pointer,
   which some ABIs do when passing a larger aggregate by-value.  */
extern int gdbarch_pass_value_as_reference_p (struct gdbarch *gdbarch);
typedef int (gdbarch_pass_value_as_reference_ftype) (struct gdbarch *gdbarch,
						     struct value *function,
						     struct type *value_type);
extern int gdbarch_pass_value_as_reference (struct gdbarch *gdbarch,
					    struct value *function,
					    struct type *value_type);
extern void set_gdbarch_pass_value_as_reference (struct gdbarch *gdbarch,
						 gdbarch_pass_value_as_reference_ftype *pass_value_as_reference);

#endif
