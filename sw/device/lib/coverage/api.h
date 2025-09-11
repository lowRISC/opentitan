// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_H_
#define OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef OT_COVERAGE_ENABLED

/**
 * Initializes the coverage counter region in RAM to an "uncovered" state.
 *
 * The validity flag is set after initialization.
 *
 * This function is no-op in non-coverage builds.
 */
void coverage_init(void);

/**
 * Triggers a coverage report dump.
 *
 * If the coverage data is valid, it compresses the counter data and sends the
 * report.
 *
 * The function is usually called from shutdown hooks (e.g., shutdown_finalize),
 * before boot stage handoff, or at the end of a test.
 *
 * This function is no-op in non-coverage builds.
 */
void coverage_report(void);

/**
 * Invalidates the coverage data.
 *
 * Called before handing off execution to a subsequent boot stage (e.g., from
 * ROM_EXT to the owner software) to prevent reporting data from a previous
 * stage.
 *
 * This function is no-op in non-coverage builds.
 */
void coverage_invalidate(void);

#else  // OT_COVERAGE_ENABLED

#define coverage_init(...) \
  do {                     \
  } while (0)
#define coverage_report(...) \
  do {                       \
  } while (0)
#define coverage_invalidate(...) \
  do {                           \
  } while (0)

#endif  // OT_COVERAGE_ENABLED

#endif  // OPENTITAN_SW_DEVICE_LIB_COVERAGE_API_H_
