/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan (test) boot ROM.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv)

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

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_rom_ext_virtual_start_address = ORIGIN(rom_ext_virtual);
_rom_ext_virtual_size = LENGTH(rom_ext_virtual);
ASSERT((_rom_ext_virtual_size <= (LENGTH(eflash) / 2)),
  "Error: rom ext flash is bigger than slot.");

_rom_digest_size = 32;
_chip_info_start = ORIGIN(rom) + LENGTH(rom) - _rom_digest_size - _chip_info_size;

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
   * Ibex interrupt vector. See test_rom_start.S for more information.
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
   * Critical static data that is accessible by both the ROM and the ROM
   * extension.
   */
  INCLUDE sw/device/silicon_creator/lib/base/static_critical.ld

  /**
   * Standard mutable data section, at the bottom of RAM. This will be
   * initialized from the .idata section at runtime by the CRT.
   */
  .data : ALIGN(4) {
    _data_start = .;
    _data_init_start = LOADADDR(.data);

    /* This will get loaded into `gp`, and the linker will use that register for
     * accessing data within [-2048,2047] of `__global_pointer$`.
     *
     * This is much cheaper (for small data) than materializing the
     * address and loading from that (which will take one extra instruction). */
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

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _data_end = .;
    _data_init_end = LOADADDR(.data) + SIZEOF(.data);

    /* This puts it in ram_main at runtime (for the VMA), but puts the section
     * into rom for load time (for the LMA). This is why `_data_init_*` uses
     * `LOADADDR`. */
  } > ram_main AT> rom

  /**
   * Immutable chip_info data, containing build-time-recorded information.
   */
  .chip_info _chip_info_start : ALIGN(4) {
    KEEP(*(.chip_info))
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
