/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan IMM_ROM_EXT.
 *
 * Portions of this file are Ibex-specific.
 *
 * The IMM_ROM_EXT is kept in the .rom_ext_immutable section in ROM, after the
 * .manifest section. This linker script targets to use slot B address, and
 * the addresses are similar to the linker script rom_ext_slot_b.ld that ROM_EXT
 * is using.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for IMM_ROM_EXT.
 */

/* Slot B starts at the half-size mark of the eFlash. */
MEMORY {
  imm_rom_ext_slot_b(rx) : ORIGIN = ORIGIN(eflash) + LENGTH(eflash) / 2 + 0x400, LENGTH = LENGTH(eflash) / 2 - 0x400
}
REGION_ALIAS("rom_ext_flash", imm_rom_ext_slot_b);

INCLUDE sw/device/silicon_creator/imm_rom_ext/imm_rom_ext_common.ld
