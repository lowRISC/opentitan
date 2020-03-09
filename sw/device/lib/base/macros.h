// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_MACROS_H_
#define OPENTITAN_SW_DEVICE_LIB_MACROS_H_

/**
 * Computes the number of variable args at compile-time.
 *
 * Currently, there is no way of knowing the number of var args at compile time.
 * This information is needed for the 'backdoor' logging to work in DV. The
 * following meta-programming enables us to get that information as long as the
 * number of var args passed is <=32.
 */
#define GET_NTH_VARIABLE_ARG(xf, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10,  \
                             x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, \
                             x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, \
                             x31, n, ...)                                      \
  n
#define SHIFT_N_VARIABLE_ARGS(...) GET_NTH_VARIABLE_ARG(__VA_ARGS__)
#define PASS_N_VARIABLE_ARGS(...)                                             \
  SHIFT_N_VARIABLE_ARGS(__VA_ARGS__, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22,  \
                        21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, \
                        7, 6, 5, 4, 3, 2, 1, 0)
#define GET_NUM_VARIABLE_ARGS(...) PASS_N_VARIABLE_ARGS(0, ##__VA_ARGS__)

#endif  // OPENTITAN_SW_DEVICE_LIB_MACROS_H_
