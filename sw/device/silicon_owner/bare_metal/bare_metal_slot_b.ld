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
 * linker script only targets Slot B.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

/* Slot B starts at the half-size mark of the eFlash plus the fixed size of the
 * ROM_EXT.
 */
 /* TODO(#9045): Move ROM_EXT size to a common location. */
_slot_start_address = ORIGIN(eflash) + (LENGTH(eflash) / 2) + 0x10000;

REGION_ALIAS("owner_flash", eflash);

INCLUDE sw/device/silicon_owner/bare_metal/bare_metal_common.ld
