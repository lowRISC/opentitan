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
 * the upper half of NVM), this linker script targets both by using a virtual
 * address. The ROM must configure the address translation before jumping to
 * to the virtual address.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_rom_ext_start_address = ORIGIN(rom_ext_virtual);
_rom_ext_size = LENGTH(rom_ext_virtual);
/*
 * Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of whichever
 * physical slot this virtual image ends up mapped into.
 */
ASSERT((_rom_ext_size <= (LENGTH(nvm) / 2 - _nvm_slot_reserved_bytes)), "Error: rom ext NVM is bigger than slot");

REGION_ALIAS("rom_ext_nvm", rom_ext_virtual);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
