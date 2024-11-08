/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * NOTE:
 * This is an incomplete common portion of ROM_EXT linker file, and should not
 * be used directly. Instead it should be included by a top level ROM_EXT slot
 * linker file.
 */

OUTPUT_ARCH(riscv)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_owner_virtual_start_address = ORIGIN(owner_virtual);
_owner_virtual_size = LENGTH(owner_virtual);

/**
 * Marking the entry point correctly for the ELF file. The signer tool will
 * transfer this value to the `entry_point` field of the manifest, which will
 * then be used by `rom_boot` to handover execution to ROM_EXT.
 */
ENTRY(_rom_ext_start_boot)

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x10000;

/*
 * The start of the .text section relative to the beginning of the associated
 * slot for use in the manifest.
 */
_manifest_code_start = _text_start - _rom_ext_start_address;
/*
 * The end of the .text section relative to the beginning of the associated slot
 * for use in the manifest.
 */
_manifest_code_end = _text_end - _rom_ext_start_address;
/*
 * The location of the entry point relative to the beginning of the associated
 * slot for use in the manifest.
 */
_manifest_entry_point = _rom_ext_start_boot - _rom_ext_start_address;
/*
 * The value kHardenedBoolFalse (0x1d4) is selected if the code is linked in
 * the flash region.  Otherwise, the value kHardenedBoolTrue (0x739) is
 * selected.
 */
_manifest_address_translation = (_text_start >= ORIGIN(eflash) &&
                                 _text_start < (ORIGIN(eflash)
                                              + LENGTH(eflash))) ? 0x1d4 : 0x739;


/**
 * NOTE: We have to align each section to word boundaries as our current
 * s19->slm conversion scripts are not able to handle non-word aligned sections.
 */
SECTIONS {
  .manifest _rom_ext_start_address : {
    KEEP(*(.manifest))
    . = ALIGN(4);
  } > rom_ext_flash

  /**
   * Immutable ROM_EXT section.
   *
   * Resides in the .text section so it is covered by the ePMP configuration
   * that enables ROM_EXT execution.
   */
  .rom_ext_immutable : ALIGN(4) {
    _text_start = .;
    _rom_ext_immutable_start = .;
    KEEP(*(.rom_ext_immutable))

    /* TODO: Remove this fallback when rom_ext_immutable section is ready. */
    KEEP(*(.rom_ext_immutable.fallback))

    /* Ensure section end is word-aligned. */
    . = ALIGN(256);
    _rom_ext_immutable_end = .;
  } > rom_ext_flash

  /**
   * Ibex interrupt vector.
   *
   * This has to be set up at a 256-byte offset, so that we can use it with
   * Ibex.
   */
  .vectors : ALIGN(256) {
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
