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
 * the upper half of NVM), this linker script only targets Slot A.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot A starts at begining of the NVM. */
_rom_ext_size = LENGTH(nvm) / 2;
_rom_ext_start_address = ORIGIN(nvm);

REGION_ALIAS("rom_ext_nvm", nvm);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
