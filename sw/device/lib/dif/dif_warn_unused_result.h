// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_

/**
 * @file
 * @brief Unused Result Warning Macro for DIFs.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Attribute for functions which return errors that must be acknowledged.
 *
 * This attribute must be used to mark all DIFs which return an error value of
 * some kind, to ensure that callers do not accidentally drop the error on the
 * ground.
 *
 * Normally, the standard way to drop such a value on the ground explicitly is
 * with the syntax `(void)expr;`, in analogy with the behavior of C++'s
 * `[[nodiscard]]` attribute.
 * However, GCC does not implement this, so the idiom `if (expr) {}` should be
 * used instead, for the time being.
 * See https://gcc.gnu.org/bugzilla/show_bug.cgi?id=25509.
 */
#define DIF_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_WARN_UNUSED_RESULT_H_
