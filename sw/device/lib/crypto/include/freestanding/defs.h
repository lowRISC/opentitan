// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_DEFS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_DEFS_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * OpenTitan's status_t is a single 32-bit word conveying either a result code
 * or an error code.
 * - The otcrypto has only one result code: The `Ok` value which is
 *   equivalent in value to kHardenedBoolTrue.
 * - The otcrypto error codes all have the MSB set and encode an error type of
 *   absl_status_t in the lower 5 bits.
 *
 *   This definition is supplied to provide the status_t definition when
 *   otcrypto is exported out of the OpenTitan repository.
 */
typedef struct status {
  int32_t value;
} status_t;

/**
 * Attribute for functions which return errors that must be acknowledged.
 */
#define OT_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_FREESTANDING_DEFS_H_
