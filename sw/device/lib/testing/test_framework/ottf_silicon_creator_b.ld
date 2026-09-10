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
 * at the Silicon Creator boot stage in slot B.
 */
_ottf_start_address = ORIGIN(ottf_storage) + (LENGTH(ottf_storage) / 2);

/*
 * Leaves `_nvm_slot_reserved_bytes` empty at the end of Slot B.
 */
MEMORY {
  ottf_creator_b(rx) : ORIGIN = _ottf_start_address,
    LENGTH = (LENGTH(ottf_storage) / 2) - _nvm_slot_reserved_bytes
}
_ottf_size = LENGTH(ottf_creator_b);

REGION_ALIAS("ottf_nvm", ottf_creator_b);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
