/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial Linker Script for OpenTitan Coverage Runtime
 *
 * This Linker Script contains all the bss sections that we need in the ELF file
 * for the coverage runtime. This script is usually included after the last RAM
 * section in the main linker script to minimize the difference between normal
 * build and coverage build.
 *
 * This partial linker script requires the main linker script to define the
 * following memory region or alias:
 * - ram_main
 */

/* BSS Sections for LLVM coverage runtime. */
__ot_coverage_bss (NOLOAD) : ALIGN(8) {
  KEEP(*(__ot_coverage_bss))

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__ot_coverage_bss) == 0,
    "__ot_coverage_bss section must be empty when coverage is disabled.");
} > ram_main :NONE

/* LLVM coverage counters. */
. = ALIGN(8);
__llvm_prf_cnts : AT(0x0) ALIGN(8) {
  /* Set gap fill pattern to 0xa5 */
  FILL(0xa5a5a5a5);

  __llvm_prf_cnts_start = .;
  KEEP(*(__llvm_prf_cnts_head))
  __llvm_prf_cnts_head_end = .;
  KEEP(*(__llvm_prf_cnts))
  __llvm_prf_cnts_values_end = .;
  . = ALIGN(8);

  __llvm_prf_cnts_end = .;

  ASSERT(
    _stack_start > ABSOLUTE(.),
    "Allocated RAM overflow to stack region");

  ASSERT(
    __llvm_prf_cnts_head_end - __llvm_prf_cnts_start <= 64,
    "Allocated more than 64 restorable head coverage counters");

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__llvm_prf_cnts) == 0,
    "__llvm_prf_cnts section must be empty when coverage is disabled.");
} > ram_main :NONE
