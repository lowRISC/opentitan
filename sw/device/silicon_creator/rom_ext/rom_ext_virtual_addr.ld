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
 * the upper half of flash), this linker script targets both by using a virtual
 * address. The ROM must configure the address translation before jumping to
 * to the virtual address.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Reserving space at the top of the RAM for the stack. */
_stack_size = 0x2000;
_stack_end = ORIGIN(ram_main) + LENGTH(ram_main);
_stack_start = _stack_end - _stack_size;

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_rom_ext_start_address = ORIGIN(rom_ext_virtual);
_rom_ext_size = LENGTH(rom_ext_virtual);
ASSERT((_rom_ext_size <= (LENGTH(eflash) / 2)), "Error: rom ext flash is bigger than slot");

REGION_ALIAS("rom_ext_flash", rom_ext_virtual);

INCLUDE sw/device/silicon_creator/rom_ext/rom_ext_common.ld
