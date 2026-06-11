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
  _static_dice_start = .;
  ASSERT(
    . == ORIGIN(ram_main) + SIZEOF(.static_critical),
    "Error: .static_dice section does not follow the .static_critical section.");

  _static_dice_cdi_0_start = .;
  KEEP(*(.static_dice.cdi_0))
  _static_dice_cdi_0_end = .;
  _static_dice_cdi_0_size = _static_dice_cdi_0_end - _static_dice_cdi_0_start;

  _static_dice_mldsa_cdi_start = .;
  KEEP(*(.static_dice.mldsa_cdi))
  _static_dice_mldsa_cdi_end = .;
  _static_dice_mldsa_cdi_size = _static_dice_mldsa_cdi_end - _static_dice_mldsa_cdi_start;

  ASSERT(
    _static_dice_cdi_0_size == 1220 || _static_dice_cdi_0_size == 0,
    "Error: .static_dice.cdi_0 section size must be 1220 or 0");
  ASSERT(
    _static_dice_mldsa_cdi_size == 18988 || _static_dice_mldsa_cdi_size == 0,
    "Error: .static_dice.mldsa_cdi section size must be 18988 or 0");
  _static_dice_end = .;
} > ram_main
