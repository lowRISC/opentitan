// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_TYPES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_TYPES_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * OTP Value type definitions used in this module.
 */
typedef enum otp_val_type {
  /**Array of `uint32_t` values.*/
  kOptValTypeUint32Buff,
  /**Array of `uint64_t` values.*/
  kOptValTypeUint64Buff,
  /**Array of `uint64_t` random values to be extracted from an entropy source
     before programming the target OTP address. */
  kOptValTypeUint64Rnd,
} otp_val_type_t;

/**
 * Defines an OTP target `offset` and `num_values` to program using either a
 * `value32` or a `value64` buffer source depending on the `type` definition.
 */
typedef struct otp_kv {
  /**OTP value type.*/
  otp_val_type_t type;
  /**
   * Target absolute address with respect to the start of the OTP memory
   * region.
   */
  uint32_t offset;
  /**
   * Number of values to configure. This is equivalent to the ARRAYSIZE of
   * either `value32` or `value64` depending on the value `type`.
   */
  uint32_t num_values;
  union {
    /**
     * Points to an `uint32_t` buffer if the `type` is set to
     * kOptValTypeUint32Buff.
     */
    const uint32_t *value32;
    /**
     * Points to an `uint64_t` buffer if the `type` is set to
     * kOptValTypeUint64Buff.
     */
    const uint64_t *value64;
  };
} otp_kv_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_TYPES_H_
