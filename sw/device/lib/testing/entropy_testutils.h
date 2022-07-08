// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_

#include "sw/device/lib/dif/dif_entropy_src.h"

/**
 * Initialize the entropy complex in auto-request mode.
 *
 * Initializes the CSRNG, EDN0, and EDN1 in automatic request mode, with EDN1
 * providing highest-quality entropy and EDN0 providing lower-quality entropy.
 * The entropy source must have been initialized separately before calling this
 * function.
 */
void entropy_testutils_auto_mode_init(void);

/**
 * Initializes the entropy complex to serve random bits to EDN0 and EDN1.
 *
 * Initializes entropy_src, csrng, EDN0 and EDN1 with default boot time
 * configuration to enable entropy distribution for testing purposes.
 */
void entropy_testutils_boot_mode_init(void);

/**
 * Wait for the entropy_src to reach a certain state.
 */
void entropy_testutils_wait_for_state(const dif_entropy_src_t *entropy_src,
                                      dif_entropy_src_main_fsm_t state);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
