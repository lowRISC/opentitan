/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * TODO(#24368): Adapt the linker script for real IMM_SECTION. This linker
 * script only works for hello-world ROM_EXT IMM_SECTION.
 */

OUTPUT_ARCH(riscv)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x10000;

ENTRY(_imm_section_start_boot)

SECTIONS {
  /**
   * Ibex interrupt vector.
   *
   * This has to be set up at a 256-byte offset, so that we can use it with
   * Ibex.
   */
  .vectors : ALIGN(256) {
    _text_start = .;
    _rom_ext_immutable_start = .;
    KEEP(*(.vectors))
  } > rom_ext_flash

  /**
   * C runtime (CRT) section, containing program initialization code.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
  } > rom_ext_flash

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
  } > rom_ext_flash

  /**
   * Shutdown text section, containing shutdown function(s).
   *
   * This must be the last executable section in the ROM_EXT flash image.
   */
  .shutdown : ALIGN(4) {
    *(.shutdown)
    *(.shutdown.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _text_end = .;
  } > rom_ext_flash

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
  } > rom_ext_flash

  /**
   * Critical static data that is accessible by both the ROM and the ROM
   * extension.
   */
  INCLUDE sw/device/silicon_creator/lib/base/static_critical.ld

  /**
   * Critical static data that is accessible by both the immutable and
   * mutable ROM extension.
   */
  INCLUDE sw/device/silicon_creator/lib/base/static_dice.ld

  /**
   * Mutable data section, at the bottom of ram_main. This will be initialized
   * from flash at runtime by the CRT.
   *
   * Load this by copying the bytes from [_data_init_start, _data_init_end] into
   * the range [_data_start, _data_end].
   */
  .data : ALIGN(4) {
    _data_start = .;
    _data_init_start = LOADADDR(.data);

    /* This will get loaded into `gp`, and the linker will use that register for
     * accessing data within [-2048,2047] of `__global_pointer$`.
     *
     * This is much cheaper (for small data) than materializing the
     * address and loading from that (which will take one extra instruction).
     */
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
    _rom_ext_immutable_end = LOADADDR(.data) + SIZEOF(.data);

    /* This puts it in ram_main at runtime (for the VMA), but puts the section
     * into flash for load time (for the LMA). This is why `_data_init_*` uses
     * `LOADADDR`.
     *
     * Using `AT>` means we don't have to keep track of the next free part of
     * flash, as we do in our other linker scripts. */
  } > ram_main AT> rom_ext_flash

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

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  INCLUDE sw/device/info_sections.ld
}
