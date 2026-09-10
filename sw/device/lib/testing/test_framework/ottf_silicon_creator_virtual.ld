/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run rom.
 */

/* This linker script is preprocessed, OPENTITAN_TOP_MEMORY_LD is a define
 * set by Bazel to point to the top's linker file. */
INCLUDE OPENTITAN_TOP_MEMORY_LD

#include "ottf_ld_top_config.ld"

/**
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the Silicon Creator boot stage in the virtual slot.
 */
_ottf_start_address = ORIGIN(rom_ext_virtual);

/*
 * Leaves `_nvm_slot_reserved_bytes` empty at the end of the physical slot.
 */
MEMORY {
  ottf_creator_virtual(rx) : ORIGIN = _ottf_start_address,
    LENGTH = LENGTH(rom_ext_virtual) - _nvm_slot_reserved_bytes
}
_ottf_size = LENGTH(ottf_creator_virtual);

REGION_ALIAS("ottf_nvm", ottf_creator_virtual);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
