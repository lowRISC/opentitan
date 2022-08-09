/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan ROM_EXT.
 *
 * Portions of this file are Ibex-specific.
 *
 * The ROM_EXT is actually kept in flash, rather than ROM. While a ROM_EXT can
 * be loaded into either Slot A (the start of flash), or Slot B (the start of
 * the upper half of flash), this linker script only targets Slot B.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot B starts at the half-size mark of the eFlash. */
_rom_ext_size = LENGTH(eflash) / 2;
_rom_ext_start_address = ORIGIN(eflash) + _rom_ext_size;

REGION_ALIAS("rom_ext_flash", eflash);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
