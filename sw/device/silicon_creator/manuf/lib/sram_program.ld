/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan SRAM program.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv);

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

_stack_end = ORIGIN(ram_main) + LENGTH(ram_main);

/**
 * DV Log offset.
 *
 * Note: This definition is required by the `sw/device/info_sections.ld` script.
 */
_dv_log_offset = 0x10000;

/* We do not use this information but it used to prevent the linker from discarding
 * the crt */
ENTRY(sram_start);

SECTIONS {
  /**
   * SRAM programs consist only of a `.data` section that contains all input
   * `.rodata`, `.data`, `.text`, and `.bss` sections.
   */
  .data ORIGIN(ram_main) + _static_critical_size : ALIGN(4) {
    /* This will get loaded into `gp`, and the linker will use that register for
     * accessing data within [-2048,2047] of `__global_pointer$`.
     *
     * This is much cheaper (for small data) than materializing the
     * address and loading from that (which will take one extra instruction).
     *
     * This must match the value used for functional tests to be able to call
     * SRAM programs from functional tests. */
    __global_pointer$ = . + 2048;

    /* Place the entry point of the SRAM program to the start of the main SRAM
     * so that we don't have to maintain a separate offset from the start of
     * the RAM to the entry point. */
    KEEP(*(.sram_start))
    KEEP(*(.crt))

    /* Place all input `.rodata`, `.data`, `.text` sections in the main SRAM.
     *
     * Small data should come before larger data. This helps to ensure small
     * globals are within 2048 bytes of the value of `gp`, making their accesses
     * hopefully only take one instruction. Other data will likely need
     * multiple instructions to load, so we're less concerned about address
     * materialisation taking more than one instruction. */
    KEEP(*(.srodata))
    KEEP(*(.srodata.*))
    KEEP(*(.rodata))
    KEEP(*(.rodata.*))
    . = ALIGN(4);
    KEEP(*(.sdata))
    KEEP(*(.sdata.*))
    KEEP(*(.data))
    KEEP(*(.data.*))
    . = ALIGN(4);
    KEEP(*(.text))
    KEEP(*(.text.*))
    . = ALIGN(4);
  } > ram_main

  /**
   * Standard BSS section. This will be zeroed at runtime by the CRT.
   */
  .bss : ALIGN(4) {
    _bss_start = .;

    /**
     * Small BSS comes before regular BSS for the same reasons as in the data
     * section.
     */
    *(.sbss)
    *(.sbss.*)
    *(.bss)
    *(.bss.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  INCLUDE sw/device/info_sections.ld
}
