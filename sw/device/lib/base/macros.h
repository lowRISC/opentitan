// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MACROS_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MACROS_H_

/**
 * @file
 * @brief Generic preprocessor macros that don't really fit anywhere else.
 */

/**
 * A variable-argument macro that expands to the number of arguments passed into
 * it, between 0 and 31 arguments.
 *
 * This macro is based off of a well-known preprocessor trick. This
 * StackOverflow post expains the trick in detail:
 * https://stackoverflow.com/questions/2308243/macro-returning-the-number-of-arguments-it-is-given-in-c
 * TODO #2026: a dummy token is required for this to work correctly.
 *
 * @param dummy a dummy token that is required to be passed for the calculation
 *              to work correctly.
 * @param ... the variable args list.
 */

// Implementation details for `GET_NUM_VARIABLE_ARGS()`.
#define GET_NUM_VARIABLE_ARGS(dummy, ...)                                      \
  SHIFT_N_VARIABLE_ARGS_(dummy, ##__VA_ARGS__, 31, 30, 29, 28, 27, 26, 25, 24, \
                         23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11,   \
                         10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0)
#define SHIFT_N_VARIABLE_ARGS_(...) GET_NTH_VARIABLE_ARG_(__VA_ARGS__)
#define GET_NTH_VARIABLE_ARG_(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, \
                              x11, x12, x13, x14, x15, x16, x17, x18, x19, \
                              x20, x21, x22, x23, x24, x25, x26, x27, x28, \
                              x29, x30, x31, n, ...)                       \
  n

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MACROS_H_
