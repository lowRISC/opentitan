/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan boot ROM.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv)
GROUP(-lgcc)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * The boot address, which indicates the location of the initial interrupt
 * vector.
 */
_boot_address = ORIGIN(rom);

_heap_size = 0xe000;
_stack_size = LENGTH(ram_main) - _heap_size;
_stack_end = ORIGIN(ram_main) + LENGTH(ram_main);
_stack_start = _stack_end - _stack_size;
_flash_start = ORIGIN(eflash);

/**
 * This symbol points at the header of the flash binary, which contains loading
 * and signing information.
 *
 * See sw/device/lib/ext/common/flash_link.ld, under the .flash_header section,
 * which populates it.
 */
_flash_header = _flash_start;

_chip_info_size = 128;
_chip_info_start = ORIGIN(rom) + LENGTH(rom) - _chip_info_size;

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x0;

/**
 * We define an entry point only for documentation purposes (and to stop LLD
 * erroring). In reality, we don't use this information within the ROM image, as
 * we start at a fixed offset.
 */
ENTRY(_reset_start);

/**
 * NOTE: We have to align each section to word boundaries as our current
 * s19->slm conversion scripts are not able to handle non-word aligned sections.
 */
SECTIONS {
  /**
   * Ibex interrupt vector. See irq_vector.S for more information.
   *
   * This has to be set up at the boot address, so that execution jumps to the
   * reset handler correctly.
   */
  .vectors _boot_address : ALIGN(4) {
    KEEP(*(.vectors))
  } > rom

  /**
   * C runtime (CRT) section, containing program initialization code.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
  } > rom

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)
  } > rom

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
  } > rom

  /**
   * "Intitial data" section, the initial values of the mutable data section
   * initialized at runtime.
   */
  .idata : ALIGN(4) {
    _data_init_start = .;
  } > rom

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
    . = ALIGN(4);
    _data_end = .;
  } > ram_main

  /**
   * Immutable chip_info data, containing build-time-recorded information.
   */
  .chip_info _chip_info_start : ALIGN(4) {
    *(.chip_info)
  } > rom

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
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  INCLUDE sw/device/info_sections.ld
}
