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
 * rom_ext_virtual must be a power of two (NAPOT remap masking) and equal
 * one NVM slot. rom.ld/test_rom.ld check this too, but for a different
 * link unit than the ROM_EXT itself.
 */
ASSERT((_rom_ext_size & (_rom_ext_size - 1)) == 0,
  "Error: rom_ext_virtual must be a power of two (NAPOT remap/ePMP).");
ASSERT(_rom_ext_size == LENGTH(nvm) / 2,
  "Error: rom_ext_virtual does not match the NVM slot size.");

/*
 * Leaves `_nvm_slot_reserved_bytes` empty at the end of the physical slot.
 */
MEMORY {
  rom_ext_virtual_usable(rx) : ORIGIN = ORIGIN(rom_ext_virtual),
    LENGTH = LENGTH(rom_ext_virtual) - _nvm_slot_reserved_bytes
}

REGION_ALIAS("rom_ext_nvm", rom_ext_virtual_usable);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
