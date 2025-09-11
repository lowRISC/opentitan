/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial Linker Script for OpenTitan Coverage Runtime
 *
 * This Linker Script contains all the rodata sections that we need in the ELF
 * file for the coverage runtime. This script is usually included after the last
 * rodata section in the main linker script to minimize the difference between
 * normal build and coverage build.
 *
 * This partial linker script requires the main linker script to define the
 * following memory region or alias:
 * - coverage_flash
 */

/**
 * Build ID for coverage profile correlation.
 */
.note.gnu.build-id : ALIGN(4) {
  _build_id_start = .;
  *(.note.build-id)
  *(.note.gnu.build-id)
  _build_id_end = .;

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(.note.gnu.build-id) == 0,
    "Build ID section must be empty when coverage is disabled.");
} > coverage_flash
