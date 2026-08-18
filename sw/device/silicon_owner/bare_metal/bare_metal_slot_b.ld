/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan first Silicon Owner stage.
 *
 * Portions of this file are Ibex-specific.
 *
 * The first Silicon Owner stage kept in NVM, and can be loaded into either
 * Slot A (lower half o the NVM), or Slot B (upper half of NVM), this
 * linker script only targets Slot B.
 */

INCLUDE OPENTITAN_TOP_MEMORY_LD

/* Slot B starts at the half-size mark of the NVM plus the fixed size of the
 * ROM_EXT.
 */
_slot_start_address = ORIGIN(nvm) + (LENGTH(nvm) / 2) + _rom_ext_size;

/* Bounded to leave `_nvm_slot_reserved_bytes` empty at the end of Slot B. */
MEMORY {
  bare_metal_slot_b(rx) : ORIGIN = _slot_start_address, LENGTH = LENGTH(nvm) / 2 - _rom_ext_size - _nvm_slot_reserved_bytes
}
REGION_ALIAS("owner_nvm", bare_metal_slot_b);

INCLUDE sw/device/silicon_owner/bare_metal/bare_metal_common.ld
