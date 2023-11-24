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

ENTRY(sram_start);

/* NOTE This linker script assumes non-page-aligned segments because we skip
 * the first _static_critical_size bytes of the SRAM and we do not want the
 * ELF segments to contain the headers as this would overwrite the contents of
 * static_critical data. */
SECTIONS {
  /* The ELF SRAM program loader will automatically read back the data of the section
   * containing the entry point to verify that it is correct. The expectation is that
   * this section is very small and only contains the code that computes the CRC of
   * everything else. For this reason, we separate the sram start+crt code from the
   * rest. */
  .sram_start ORIGIN(ram_main) + _static_critical_size : ALIGN(4) {
    _crc_start = .;
    /* Place the entry point of the SRAM program to the start of the main SRAM
     * so that we don't have to maintain a separate offset from the start of
     * the RAM to the entry point for VMEM files. */
    KEEP(*(.sram_start))
    . = ALIGN(256);
  } > ram_main

  .vectors : ALIGN (256){
    KEEP(*(.vectors))
    . = ALIGN(4);
  } > ram_main

  .text : ALIGN(4) {
    KEEP(*(.crt))
    KEEP(*(.text))
    KEEP(*(.text.*))
    . = ALIGN(4);
  } > ram_main

  .rodata : ALIGN(4) {
    KEEP(*(.rodata))
    KEEP(*(.rodata.*))
    . = ALIGN(4);
    __rodata_end = .;
  } > ram_main

  .data : ALIGN(4) {
    /* This will get loaded into `gp`, and the linker will use that register for
     * accessing data within [-2048,2047] of `__global_pointer$`.
     *
     * This is much cheaper (for small data) than materializing the
     * address and loading from that (which will take one extra instruction).

     * Since the .data section is small for SRAM programs, it doesn't make a big
     * difference to distinguish data from small data. */
    __global_pointer$ = . + 2048;

    KEEP(*(.data))
    KEEP(*(.data.*))

    /* Place all small data sections together. */
    KEEP(*(.srodata))
    KEEP(*(.srodata.*))
    KEEP(*(.sdata))
    KEEP(*(.sdata.*))
    . = ALIGN(4);
    _crc_end = .;
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
