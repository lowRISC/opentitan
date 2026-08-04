/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan first Silicon Owner stage.
 *
 * Portions of this file are Ibex-specific.
 *
 * The first Silicon Owner stage is kept in NVM, and can be loaded into either
 * Slot A, or Slot B. This linker script a single binary that can be executed in
 * both slots.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_slot_start_address = ORIGIN(owner_virtual) + _rom_ext_size;

/*
 * Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of whichever
 * physical slot this virtual image ends up mapped into.
 */
MEMORY {
  bare_metal_slot_virtual(rx) : ORIGIN = _slot_start_address, LENGTH = LENGTH(owner_virtual) - _rom_ext_size - _nvm_slot_reserved_bytes
}
_slot_size = LENGTH(bare_metal_slot_virtual);

REGION_ALIAS("owner_nvm", bare_metal_slot_virtual);

INCLUDE sw/device/silicon_owner/bare_metal/bare_metal_common.ld
