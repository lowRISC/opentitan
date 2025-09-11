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

#else  // OT_COVERAGE_INSTRUMENTED

#define COVERAGE_ASM_INIT(...)
#define COVERAGE_ASM_TRANSPORT_INIT(...)

#endif  // OT_COVERAGE_INSTRUMENTED

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_ASM_H_
