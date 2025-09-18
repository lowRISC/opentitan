/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial Linker Script for OpenTitan Coverage Tools
 *
 * This Linker Script contains all the info sections that we need in the ELF
 * file for the coverage tools.
 *
 * This script is included by the global one (sw/device/info_sections.ld).
 */

/**
 * Profile data and names are moved to the INFO section due to device-side
 * memory constraints. These data will be used with the counters on the host
 * to reconstruct the LLVM profile.
 */
__llvm_prf_data 0x0 (INFO) : ALIGN(8) {
  __llvm_prf_data_start = .;
  KEEP(*(__llvm_prf_data))
  __llvm_prf_data_end = .;

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__llvm_prf_data) == 0,
    "__llvm_prf_data section must be empty when coverage is disabled.");
}

/**
 * Profile data and names are moved to the INFO section due to device-side
 * memory constraints. These data will be used with the counters on the host
 * to reconstruct the LLVM profile.
 */
__llvm_prf_names 0x0 (INFO) : ALIGN(1) {
  __llvm_prf_names_start = .;
  KEEP(*(__llvm_prf_names))
  __llvm_prf_names_end = .;

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__llvm_prf_names) == 0,
    "__llvm_prf_names section must be empty when coverage is disabled.");
}

/**
 * Sections required by the `llvm-cov` tool to map the collected profiles to
 * source code lines.
 */
__llvm_covmap 0x0 (INFO) : ALIGN(8) {
  KEEP(*(__llvm_covmap))

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__llvm_covmap) == 0,
    "__llvm_covmap section must be empty when coverage is disabled.");
}

/**
 * Sections required by the `llvm-cov` tool to map the collected profiles to
 * source code lines.
 */
__llvm_covfun 0x0 (INFO) : ALIGN(8) {
  KEEP(*(__llvm_covfun))

  ASSERT(
    DEFINED(_ot_coverage_enabled) || SIZEOF(__llvm_covfun) == 0,
    "__llvm_covfun section must be empty when coverage is disabled.");
}
