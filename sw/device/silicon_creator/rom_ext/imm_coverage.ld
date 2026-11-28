/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Shared SRAM boundary for immutable ROM_EXT (`imm_section`) coverage data.
 *
 * In coverage builds, `imm_section` places its coverage runtime BSS and
 * single-byte counters in `[_imm_coverage_region_start, _stack_start)`, while
 * mutable `ROM_EXT` asserts that its own `.bss` and coverage counters end at
 * or below `_imm_coverage_region_start`.
 */
_imm_coverage_region_start = _stack_start - 0x2800;
