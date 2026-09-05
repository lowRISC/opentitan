/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan (stub) boot ROM.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

INCLUDE OPENTITAN_TOP_MEMORY_LD

/**
 * The boot address, which indicates the location of the initial interrupt
 * vector.
 */
_boot_address = ORIGIN(rom);

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
   * Ibex interrupt vector. See stub_rom_start.S for more information.
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
}
