/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial Linker Script for OpenTitan Device Executables
 *
 * This Linker Script controls all the sections that we need in the ELF file for
 * a device executable, but which are not mapped into memory or otherwise
 * allocated on the device itself.
 *
 * These contain amongst other things:
 * - debugging information needed by DV logging,
 * - DWARF Sections
 * - RISC-V Attributes sections
 *
 * This is also where we specify the sections to discard, because it is a common
 * file between all our other linker scripts.
 *
 * This partial linker script requires the main linker script to define the
 * following symbols:
 * - _dv_log_offset
 */

/*
 * Start DV Sections.
 *
 * The following sections are used by DV to implement logging in an
 * alternate way, which enables simulation speed up by completely avoiding
 * any string format processing or even the actual transmission of log data
 * to a real peripheral.
 *
 * These sections are marked as dummy so that they can still be extracted
 * using readelf or similar utilities. As such, the content in these sections
 * is not relevant for the actual SW code and can be safely discarded.
 */

/**
 * The following section contains log fields constructed from the logs using
 * the log_fields_t struct defined in sw/device/lib/runtime/log.h. The size of
 * each log field is fixed - 20 bytes.
 */
.logs.fields _dv_log_offset (INFO): {
  *(.logs.fields)
}

/*
 * End DV Sections
 */

/* ELF-internal Sections. */
.symtab 0x0 : { *(.symtab) }
.strtab 0x0 : { *(.strtab) }
.shstrtab 0x0 : { *(.shstrtab) }

/* Preserve RISC-V Attributes */
.riscv.attributes 0x0 : { *(.riscv.attributes) }

/* Preserve Debug Info in ELF Files */
.debug_info 0x0 : { *(.debug_info) }
.debug_abbrev 0x0 : { *(.debug_abbrev) }
.debug_aranges 0x0 : { *(.debug_aranges) }
.debug_line 0x0 : { *(.debug_line) }
.debug_loc 0x0 : { *(.debug_loc) }
.debug_ranges 0x0 : { *(.debug_ranges) }
.debug_str 0x0 : { *(.debug_str) }
.debug_frame 0x0 : { *(.debug_frame) }

/* Discarded Sections (Not needed in device images). */
/DISCARD/ : {
  /* We don't keep unwind information */
  *(.eh_frame)
  *(.eh_frame_hdr)

  /* Compiler Information */
  *(.comment)
  *(.comment.*)

  /* Other Notes */
  *(.note)
  *(.note.*)

  /* Relocations */
  *(.rela.*)
  *(.rela.dyn)

  /* STAB Debugging Info - We Use DWARF */
  *(.stab)
  *(.stab.*)
  *(.stabstr)

  /* COMMON Sections */
  *(COMMON)
}
