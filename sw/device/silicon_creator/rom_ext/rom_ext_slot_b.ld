/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan ROM_EXT.
 *
 * Portions of this file are Ibex-specific.
 *
 * The ROM_EXT is actually kept in NVM, rather than ROM. While a ROM_EXT can
 * be loaded into either Slot A (the start of NVM), or Slot B (the start of
 * the upper half of NVM), this linker script only targets Slot B.
 */

INCLUDE OPENTITAN_TOP_MEMORY_LD

/* Slot B starts at the half-size mark of the NVM. */
_rom_ext_size = LENGTH(nvm) / 2;
_rom_ext_start_address = ORIGIN(nvm) + _rom_ext_size;

/* Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of Slot B. */
MEMORY {
  rom_ext_slot_b(rx) : ORIGIN = _rom_ext_start_address, LENGTH = LENGTH(nvm) / 2 - _nvm_slot_reserved_bytes
}
REGION_ALIAS("rom_ext_nvm", rom_ext_slot_b);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
