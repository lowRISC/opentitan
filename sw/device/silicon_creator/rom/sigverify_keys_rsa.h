// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_RSA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_RSA_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"
#include "sw/device/silicon_creator/rom/sigverify_keys.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An RSA public key stored in ROM.
 *
 * This struct must start with the common initial sequence
 * `sigverify_rom_key_header_t`.
 */
typedef struct sigverify_rom_rsa_key_entry {
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
  /**
   * An RSA public key.
   */
  sigverify_rsa_key_t key;
} sigverify_rom_rsa_key_entry_t;

OT_ASSERT_MEMBER_OFFSET(sigverify_rom_rsa_key_entry_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_rsa_key_entry_t, key.n.data[0], 4);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_key_header_t, key_type, 0);
OT_ASSERT_MEMBER_OFFSET(sigverify_rom_key_header_t, key_id, 4);

/**
 * Union type to inspect the common initial sequence of RSA public keys stored
 * in ROM.
 */
typedef union sigverify_rom_rsa_key {
  /**
   * Common initial sequence.
   */
  sigverify_rom_key_header_t key_header;
  /**
   * Actual RSA public key entry.
   */
  sigverify_rom_rsa_key_entry_t entry;
} sigverify_rom_rsa_key_t;

static_assert(
    sizeof(sigverify_rom_rsa_key_entry_t) == sizeof(sigverify_rom_rsa_key_t),
    "Size of an RSA public key entry must be equal to the size of a key");

/**
 * Number of RSA public keys.
 */
extern const size_t kSigverifyRsaKeysCnt;

/**
 * Step size to use when checking RSA public keys.
 *
 * This must be coprime with and less than `kSigverifyNumRsaKeys`.
 * Note: Step size is not applicable when `kSigverifyNumRsaKeys` is 1.
 */
extern const size_t kSigverifyRsaKeysStep;

/**
 * Public keys for signature verification.
 */
extern const sigverify_rom_rsa_key_t kSigverifyRsaKeys[];

/**
 * Returns the key with the given ID.
 *
 * This function returns the key only if it can be used in the given life cycle
 * state and is valid in OTP. OTP check is performed only if the device is in a
 * non-test operational state (PROD, PROD_END, DEV, RMA).
 *
 * @param key_id A key ID.
 * @param lc_state Life cycle state of the device.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_rsa_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_rsa_key_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_RSA_H_
