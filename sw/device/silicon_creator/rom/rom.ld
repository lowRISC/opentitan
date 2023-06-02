/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan ROM.
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
_rom_boot_address = ORIGIN(rom);

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_rom_ext_virtual_start_address = ORIGIN(rom_ext_virtual);
_rom_ext_virtual_size = LENGTH(rom_ext_virtual);
ASSERT((_rom_ext_virtual_size <= (LENGTH(eflash) / 2)),
  "Error: rom ext flash is bigger than slot.");

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x0;

/**
 * This symbol is used as a jump target when an error is detected by the
 * hardened shadow call stack implementation. We set it to 0 which will
 * trigger an instruction access exception.
 *
 * If a compiler without hardened shadow call stack support is used this
 * symbol will be ignored.
 */
__abi_shutdown$ = 0x0;

/**
 * Physical Memory Protection (PMP) encoded address register values.
 *
 * Some addresses required for PMP entries are known only at link time.
 * These addresses are encoded here so that no calculations need to be
 * performed at runtime.
 *
 * See The RISC-V Instruction Set Manual Volume II: Privileged Architecture
 * for more information about PMP address register encodings.
 */
_epmp_text_tor_lo = _text_start / 4;
_epmp_text_tor_hi = _text_end / 4;
_epmp_stack_guard_na4 = _stack_start / 4;

ENTRY(_rom_start_boot);

/**
 * NOTE: We have to align each section to word boundaries as our current
 * s19->slm conversion scripts are not able to handle non-word aligned sections.
 */
SECTIONS {
  /**
   * Ibex interrupt vector. See rom_init.S for more information.
   *
   * This has to be set up at the boot address, so that execution jumps to the
   * reset handler correctly.
   */
  .vectors _rom_boot_address : ALIGN(256) {
    _text_start = .;
    KEEP(*(.vectors))
  } > rom

  /**
   * C runtime (CRT) section, containing program initialization code.
   *
   * This is a separate section to `.text` so that the jumps inside `.vectors`
   * will fit into the instruction encoding.
   */
  .crt : ALIGN(4) {
    /* Pad with zeros. */
    FILL(0x0000)
    KEEP(*(.crt))
    /* .crt must fit in the ePMP RX region at reset. */
    ASSERT(
        SIZEOF(.vectors) + SIZEOF(.crt) <= _epmp_reset_rx_size,
        "Error: .crt overflows reset ePMP region");
    . = MAX(., _epmp_reset_rx_size - SIZEOF(.vectors));
  } > rom

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)


    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
  } > rom

  /**
   * Shutdown text section, containing shutdown function(s).
   *
   * This must be the last executable section in the ROM.
   */
  .shutdown : ALIGN(4) {
    *(.shutdown)
    *(.shutdown.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _text_end = .;
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
   * OpenTitan ROM does not have a mutable `.data` section.
   */
  .data (NOLOAD) : {
    *(.sdata)
    *(.sdata.*)
    *(.data)
    *(.data.*)

    /* Tests are an exception to the rule that .data must be empty */
    ASSERT(
        (DEFINED(rom_test) ? 0 : SIZEOF(.data)) == 0,
        "Error: .data section must be empty");
  } > ram_main

  /**
   * Standard BSS section. This will be zeroed at runtime by the CRT.
   */
  .bss : ALIGN(4) {
    _bss_start = .;

    /* This will get loaded into `gp`, and the linker will use that register for
     * accessing data within [-2048,2047] of `__global_pointer$`.
     *
     * This is much cheaper (for small data) than materializing the
     * address and loading from that (which will take one extra instruction).
     */
    __global_pointer$ = . + 2048;

    /* Small BSS should come before regular BSS. This helps to ensure small
     * globals are within 2048 bytes of the value of `gp`, making their accesses
     * hopefully only take one instruction. */
    *(.sbss)
    *(.sbss.*)
    *(.bss)
    *(.bss.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  /**
   * Immutable chip_info data, containing build-time-recorded information.
   *
   * This is the last thing in rom.
   */
  .chip_info _chip_info_start : ALIGN(4) {
    KEEP(*(.chip_info))
  } > rom

  INCLUDE sw/device/info_sections.ld
}
