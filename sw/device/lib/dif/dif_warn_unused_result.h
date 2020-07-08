// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_

/**
 * @file
 * @brief Unused Result Warning Macro for DIFs.
 */

/**
 * Attribute for functions which return errors that must be acknowledged.
 *
 * This attribute must be used to mark all DIFs which return an error value of
 * some kind, to ensure that callers do not accidentally drop the error on the
 * ground.
 */
#define DIF_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_
