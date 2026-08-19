/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run BL0 tests.
 */

/* This linker script is preprocessed, OPENTITAN_TOP_MEMORY_LD is a define
 * set by Bazel to point to the top's linker file. */
INCLUDE OPENTITAN_TOP_MEMORY_LD

#include "ottf_ld_top_config.ld"

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_ottf_start_address = ORIGIN(owner_virtual) + _rom_ext_size;

/*
 * Leaves `_nvm_slot_reserved_bytes` empty at the end of the physical slot.
 */
MEMORY {
  ottf_owner_virtual(rx) : ORIGIN = _ottf_start_address, LENGTH = LENGTH(owner_virtual) - _rom_ext_size - _nvm_slot_reserved_bytes
}
_ottf_size = LENGTH(ottf_owner_virtual);
ASSERT((_ottf_size <= (LENGTH(ottf_storage) / 2)),
  "Error: BL0 NVM is bigger than slot.");

REGION_ALIAS("ottf_nvm", ottf_owner_virtual);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
