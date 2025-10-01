// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_

#ifdef OT_COVERAGE_INSTRUMENTED

/**
 * Initializes the coverage counter region in RAM to an "uncovered" state.
 *
 * The validity flag is set after initialization.
 *
 * This function is no-op in non-coverage builds.
 */
#define COVERAGE_ASM_INIT() call coverage_init;

/**
 * Initializes the transport runtime to send coverage report.
 *
 * This function is no-op in non-coverage builds.
 */
#define COVERAGE_ASM_TRANSPORT_INIT() call coverage_transport_init;

/**
 * Marks a specific coverage point as hit.
 *
 * This function is no-op in non-coverage builds.
 *
 * @param kTemp A temporary register that will be clobbered.
 * @param kIndex The index of the counter to mark.
 */
#define COVERAGE_ASM_AUTOGEN_MARK(kTemp, kIndex) \
  lui kTemp, % hi(.L__asm_profc + kIndex);       \
  sb zero, % lo(.L__asm_profc + kIndex)(kTemp)

#else  // OT_COVERAGE_INSTRUMENTED

#define COVERAGE_ASM_INIT(...)
#define COVERAGE_ASM_TRANSPORT_INIT(...)
#define COVERAGE_ASM_AUTOGEN_MARK(...)

#endif  // OT_COVERAGE_INSTRUMENTED

#define COVERAGE_ASM_MANUAL_MARK COVERAGE_ASM_AUTOGEN_MARK

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_
