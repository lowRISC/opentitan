/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan first Silicon Owner stage.
 *
 * Portions of this file are Ibex-specific.
 *
 * The first Silicon Owner stage is kept in flash, and can be loaded into either
 * Slot A, or Slot B. This linker script a single binary that can be executed in
 * both slots.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Reserving space at the top of the RAM for the stack. */
_stack_size = 0x2000;
_stack_end = ORIGIN(ram_main) + LENGTH(ram_main);
_stack_start = _stack_end - _stack_size;

/**
 * Symbols to be used in the setup of the address translation for ROM_EXT.
 */
_slot_start_address = ORIGIN(owner_virtual) + 64K;
_slot_size = LENGTH(owner_virtual) - 64K;

REGION_ALIAS("owner_flash", owner_virtual);

INCLUDE sw/device/silicon_owner/bare_metal/bare_metal_common.ld
