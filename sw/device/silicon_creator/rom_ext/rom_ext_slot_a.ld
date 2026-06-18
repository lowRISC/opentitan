/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan ROM_EXT.
 *
 * Portions of this file are Ibex-specific.
 *
 * The ROM_EXT is actually kept in flash, rather than ROM. While a ROM_EXT can
 * be loaded into either Slot A (the start of flash), or Slot B (the start of
 * the upper half of flash), this linker script only targets Slot A.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot A starts at begining of the eFlash. */
_rom_ext_size = LENGTH(eflash) / 2;
_rom_ext_start_address = ORIGIN(eflash);

<<<<<<< HEAD
REGION_ALIAS("rom_ext_flash", eflash);
=======
REGION_ALIAS("rom_ext_nvm", rram);
>>>>>>> cb897020ae ([rom_ext,sw] rename section rom_ext_flash to rom_ext_nvm)

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
