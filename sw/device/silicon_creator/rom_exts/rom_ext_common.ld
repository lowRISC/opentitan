/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * NOTE:
 * This is an incomplete common portion of ROM_EXT linker file, and should not
 * be used directly. Instead it should be included by a top level ROM_EXT slot
 * linker file.
 */

OUTPUT_ARCH(riscv)
GROUP(-lgcc)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x10000;

/**
 * Marking the entrypoint correctly for the ELF file. In reality, we will end up
 * using a hard-coded offset from the slot start, as we don't have the ELF info
 * around once we have the image, and the entry offset is static in the image
 * format.
 */
ENTRY(_rom_ext_start_boot)

/**
 * NOTE: We have to align each section to word boundaries as our current
 * s19->slm conversion scripts are not able to handle non-word aligned sections.
 */
SECTIONS {
  .rom_ext_manifest _slot_start_address : {
    KEEP(*(.rom_ext_manifest))
  } > eflash

  /**
   * Ibex interrupt vector.
   *
   * This has to be set up at a 256-byte offset, so that we can use it with
   * Ibex. This section includes the ROM_EXT entry address.
   */
  .vectors : ALIGN(256) {
    KEEP(*(.vectors))
  } > eflash

  /**
   * C runtime (CRT) section, containing program initialization code.
   *
   * This is a separate section to `.text` so that the jumps inside `.vectors`
   * will fit into the instruction encoding.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
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
   * Mutable data section, at the bottom of ram_main. This will be initialized
   * from flash at runtime by the CRT.
   *
   * Load this by copying the bytes from [_data_init_start, _data_init_end] into
   * the range [_data_start, _data_end].
   */
  .data ORIGIN(ram_main) : ALIGN(4) {
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
  } > ram_main AT> eflash

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

  /**
   * ROM_EXT Image End Section.
   *
   * This is a dummy section required for correctly calculating the ROM_EXT
   * image length, for the manifest. See the comments in `rom_ext_manifest.S`
   * for more information.
   *
   * If you add more sections to eflash, ensure they come before this section.
   *
   * This section must be LOAD, or the image size won't be calculated correctly.
   */
  .rom_ext_end : ALIGN(4) {
    KEEP(*(.rom_ext_end))
  } > eflash

  INCLUDE sw/device/info_sections.ld
}
