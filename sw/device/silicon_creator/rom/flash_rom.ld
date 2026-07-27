/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan Flash ROM.
 *
 * Portions of this file are Ibex-specific.
 *
 * The Flash ROM is a ROM variant that is stored at the end of the flash region.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

_rom_end_address = ORIGIN(eflash) + LENGTH(eflash);
_rom_boot_address = _rom_end_address - _flash_rom_size;

_chip_info_end = _rom_end_address;
_chip_info_start = _chip_info_end - _chip_info_size;

REGION_ALIAS("rom_region", eflash);

INCLUDE sw/device/silicon_creator/rom/rom_common.ld
