/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan flash binaries.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv)
GROUP(-lgcc)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/**
 * Memory definitions are auto-generated.
 */
INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Reserving 32 bytes at the top of the RAM for test utils. */
_test_reserved_size = 0x20;

/**
 * The stack starts at the end of RAM right after the 32 reserved bytes and grows down.
 * It is zeroed out so a size must be provided.
 */
_stack_size = 0x2000 - _test_reserved_size; /* ~8kb stack */
_stack_start = ORIGIN(ram_main) + LENGTH(ram_main) - _test_reserved_size;
_stack_end = _stack_start - _stack_size;

SECTIONS {
  /**
   * The flash header. This will eventually contain other stuff, like a
   * signature, but for now it's just the entry point at offset zero.
   */
  .flash_header ORIGIN(eflash) : ALIGN(4) {
    /**
     * NOTE:ld scripts do not provide a mechanism to refer to ENTRY,
     * so we just harcode the _start symbol.
     */
    LONG(_start)
  } > eflash

  /**
   * C runtime (CRT) section, containing program initialization code.
   *
   * We don't use ENTRY, so the start of |flash| acts as the entrypoint. Since
   * the CRT is the first thing that needs to run, it goes at the top.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
    *(.crt)
  } > eflash

  /**
   * Ibex interrupt vectors. See 'ibex_interrupt_vectors.S' for more
   * information.
   */
  .vectors : {
    *(.vectors)
  } > eflash

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)
  } > eflash

  /**
   * Read-only data section, containing all large compile-time constants, like
   * strings.
   */
  .rodata : ALIGN(4) {
    /* Small read-only data comes before regular read-only data for the same
     * reasons as in the data section */
    *(.srodata)
    *(.srodata.*)
    *(.rodata)
    *(.rodata.*)
  } > eflash

  /**
   * "Intitial data" section, the initial values of the mutable data section
   * initialized at runtime.
   */
  .idata : ALIGN(4) {
    _data_init_start = .;
  } > eflash

  /**
   * Standard mutable data section, at the bottom of RAM. This will be
   * initialized from the .idata section at runtime by the CRT.
   */
  .data ORIGIN(ram_main): AT(_data_init_start) ALIGN(4) {
    _data_start = .;
    __global_pointer$ = . + 2048;

    /* Small data should come before larger data. This helps to ensure small
     * globals are within 2048 bytes of the value of `gp`, making their accesses
     * hopefully only take one instruction. */
    *(.sdata)
    *(.sdata.*)

    /* Other data will likely need multiple instructions to load, so we're less
     * concerned about address materialisation taking more than one instruction.
     */
    *(.data)
    *(.data.*)
    _data_end = .;
  } > ram_main

  /**
   * Standard BSS section. This will be zeroed at runtime by the CRT.
   */
  .bss : ALIGN(4) {
    _bss_start = .;
    /* Small BSS comes before regular BSS for the same reasons as in the data
     * section */
    *(.sbss)
    *(.sbss.*)
    *(.bss)
    *(.bss.*)
    *(COMMON)
    _bss_end = .;
  } > ram_main

  /**
   * STAB debug table.
   */
  .stab 0x0 (NOLOAD): {
    *(.stab)
  }

  /**
   * STAB debug strings.
   */
  .stabstr 0x0 (NOLOAD): {
    *(.stabstr)
  }

  /**
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
   * the log_fields_t struct defined in sw/device/lib/base/log.h. The size of
   * each log field is fixed - 20 bytes, which is used as the delimiter.
   */
  .logs.fields 0x10000 (DSECT): {
    *(.logs.fields)
  }
}
