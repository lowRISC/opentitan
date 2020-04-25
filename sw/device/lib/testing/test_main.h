// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_

/**
 * Runs the SW test.
 *
 * This method is defined externally in a standalone SW test source linked to
 * `main` as a library. It is a fully contained test in itself.
 *
 * @return success or failure of the test in boolean.
 */
bool test_main(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_MAIN_H_
