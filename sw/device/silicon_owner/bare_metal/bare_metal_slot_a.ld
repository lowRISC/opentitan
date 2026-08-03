/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan first Silicon Owner stage.
 *
 * Portions of this file are Ibex-specific.
 *
 * The first Silicon Owner stage kept in flash, and can be loaded into either
 * Slot A (lower half o the flash), or Slot B (upper half of flash), this
 * linker script only targets Slot A.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot A starts at the start of the NVM plus the fixed size of the first
 * Silicon Owner stage */
_slot_start_address = ORIGIN(nvm) + _rom_ext_size;

/* Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of Slot A. */
MEMORY {
  bare_metal_slot_a(rx) : ORIGIN = _slot_start_address, LENGTH = LENGTH(nvm) / 2 - _rom_ext_size - _nvm_slot_reserved_bytes
}
REGION_ALIAS("owner_nvm", bare_metal_slot_a);

INCLUDE sw/device/silicon_owner/bare_metal/bare_metal_common.ld
