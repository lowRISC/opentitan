// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_

/**
 * Initializes the entropy complex to serve random bits to EDN0 and EDN1.
 *
 * Initializes entropy_src, csrng, EDN0 and EDN1 with default boot time
 * configuration to enable entropy distribution for testing purposes.
 */
void entropy_testutils_boot_mode_init(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ENTROPY_TESTUTILS_H_
