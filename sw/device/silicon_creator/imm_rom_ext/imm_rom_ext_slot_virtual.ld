/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan IMM_ROM_EXT.
 *
 * Portions of this file are Ibex-specific.
 *
 * The IMM_ROM_EXT is kept in the .rom_ext_immutable section in ROM, after the
 * .manifest section. This linker script targets to use virtual address, and
 * the addresses are similar to the linker script rom_ext_slot_virtual.ld that
 * ROM_EXT is using.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for IMM_ROM_EXT.
 */

MEMORY {
  imm_rom_ext_virtual(rx) : ORIGIN = ORIGIN(rom_ext_virtual) + 0x400, LENGTH = 0x80000 - 0x400
}
REGION_ALIAS("rom_ext_flash", imm_rom_ext_virtual);

INCLUDE sw/device/silicon_creator/imm_rom_ext/imm_rom_ext_common.ld
