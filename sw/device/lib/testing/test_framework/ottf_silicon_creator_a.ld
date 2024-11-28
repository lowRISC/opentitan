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

INCLUDE @@TOP_MEMORY_LD@@
INCLUDE @@OTTF_LD_ALIAS@@

/**
 * Symbols to be used in the setup of the address translation for the OTTF run
 * at the Silicon Creator boot stage in slot A.
 */
_ottf_size = LENGTH(ottf_flash) / 2;
_ottf_start_address = ORIGIN(ottf_flash);

INCLUDE @@OTTF_LD_COMMON@@
