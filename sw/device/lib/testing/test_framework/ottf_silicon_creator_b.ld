/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for OpenTitan OTTF-launched test binaries.
 *
 * Portions of this file are Ibex-specific.
 *
 * This linker script generates a binary to run rom.
 */

INCLUDE hw/top_darjeeling/sw/autogen/top_darjeeling_memory.ld

/**
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the Silicon Creator boot stage in slot B.
 */
_ottf_size = LENGTH(ram_ctn) / 2;
_ottf_start_address = ORIGIN(ram_ctn) + _ottf_size;

REGION_ALIAS("ottf_flash", ram_ctn);

INCLUDE sw/device/lib/testing/test_framework/ottf_common.ld
