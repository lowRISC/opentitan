// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEST_BASE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEST_BASE_H_

/**
 * @file
 * @brief Shared helpers for DIF unit tests.
 */

#include <stdbool.h>

#include "gtest/gtest.h"
#include "sw/device/lib/dif/dif_base.h"

/**
 * Creates a test expectation for `expr_` to evaluate to `kDifOk`.
 */
#define EXPECT_DIF_OK(expr_) EXPECT_EQ(expr_, kDifOk)

/**
 * Creates a test assertion for `expr_` to evaluate to `kDifOk`.
 */
#define ASSERT_DIF_OK(expr_) ASSERT_EQ(expr_, kDifOk)

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEST_BASE_H_
