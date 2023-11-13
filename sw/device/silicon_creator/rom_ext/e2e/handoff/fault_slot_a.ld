/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan first Silicon Owner stage.
 *
 * Portions of this file are Ibex-specific.
 *
 * The first Silicon Owner stage kept in flash, and can be loaded into either
 * Slot A (lower half o the flash), or Slot B (upper half of flash), this
 * linker script only targets Slot A.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot A starts at the start of the eFlash plus the fixed size of the first
 * Silicon Owner stage */
 /* TODO(#9045): Move ROM_EXT size to a common location. */
_slot_start_address = ORIGIN(eflash) + 0x10000;

REGION_ALIAS("owner_flash", eflash);

INCLUDE sw/device/silicon_creator/rom_ext/e2e/handoff/fault_common.ld
