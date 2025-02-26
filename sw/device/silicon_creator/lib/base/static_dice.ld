/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * DICE variables stored in the .static_dice section of RAM.
 *
 * These variables are transferred from immutable ROM_EXT to mutable ROM_EXT.
 *
 * This file should be included inside of a `SECTIONS` block where a
 * `ram_main` memory is defined, and should come before all other main
 * memory sections and after the .static_critical section.
 */

.static_dice (NOLOAD) : ALIGN(4) {
  ASSERT(
    . == ORIGIN(ram_main) + SIZEOF(.static_critical),
    "Error: .static_dice section does not follow the .static_critical section.");

  KEEP(*(.static_dice.cdi_0))

  ASSERT(
    SIZEOF(.static_dice) == 1220,
    "Error: .static_dice section size has changed");
} > ram_main
