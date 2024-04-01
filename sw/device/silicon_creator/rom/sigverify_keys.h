// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/rom/sigverify_key_types.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of key validity entries per OTP word.
   *
   * Validity of each public key is encoded using a byte-sized
   * `hardened_byte_bool_t` in the `CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN` OTP
   * item. Size of a `hardened_byte_bool_t` is 1 byte, thus each 32-bit OTP word
   * has 4 entries.
   */
  kSigverifyNumEntriesPerOtpWord = sizeof(uint32_t),
};

/**
 * Gets the ID of a public key.
 *
 * ID of an RSA key is the least significant word of its modulus. ID of an SPX
 * key is its least significant word. This function leverages the common initial
 * sequence of both types of keys to get their IDs in a generic manner.
 *
 * Callers must make sure that `key` is valid before calling this function.
 *
 * @param key A public key.
 * @return ID of the key.
 */
OT_WARN_UNUSED_RESULT
inline uint32_t sigverify_rom_key_id_get(
    const sigverify_rom_key_header_t *key) {
  return key->key_id;
}

/**
 * Input parameters for `sigverify_key_get()`.
 */
typedef struct sigverify_key_get_in_params {
  /**
   * A key ID.
   */
  uint32_t key_id;
  /**
   * Life cycle state of the device.
   */
  lifecycle_state_t lc_state;
  /**
   * Array in which the requested key is searched for.
   */
  const sigverify_rom_key_header_t *key_array;
  /**
   * Offset of the OTP item that determines the validity of the keys.
   */
  size_t otp_offset;
  /**
   * Number of keys in `key_array`.
   */
  size_t key_cnt;
  /**
   * Size of each entry in `key_array`.
   */
  size_t key_size;
  /**
   * Step size to use when looking for public keys.
   *
   * This must be coprime with and less than `key_cnt`.
   * Note: Step size is not applicable when `key_cnt` is 1.
   */
  size_t step;
} sigverify_key_get_in_params_t;

/**
 * Returns the key with the given ID.
 *
 * This function returns the key only if it can be used in the given life cycle
 * state and is valid in OTP. OTP check is performed only if the device is in a
 * non-test operational state (PROD, PROD_END, DEV, RMA).
 *
 * @param in_params Input parameters.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_key_get(sigverify_key_get_in_params_t in_params,
                              const sigverify_rom_key_header_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_H_
