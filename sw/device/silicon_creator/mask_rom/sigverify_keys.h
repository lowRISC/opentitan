// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of RSA public keys.
   */
  kSigVerifyNumRsaKeys = 2,
  /**
   * Number of key validity entries per OTP word.
   *
   * Validity of each public key is encoded using a byte-sized
   * `hardened_byte_bool_t` in the `CREATOR_SW_CFG_KEY_IS_VALID` OTP item. Size
   * of a `hardened_byte_bool_t` is 1 byte, thus each 32-bit OTP word has 4
   * entries.
   */
  kSigverifyNumEntriesPerOtpWord = sizeof(uint32_t),
};

/**
 * Key types.
 *
 * The life cycle states in which a key can be used depend on its type.
 */
typedef enum sigverify_key_type {
  /**
   * A key used for manufacturing, testing, and RMA.
   *
   * Keys of this type can be used only in TEST_UNLOCKED* and RMA life cycle
   * states.
   */
  kSigverifyKeyTypeTest,
  /**
   * A production key.
   *
   * Keys of this type can be used in all operational life cycle states, i.e.
   * states in which CPU execution is enabled.
   */
  kSigverifyKeyTypeProd,
  /**
   * A development key.
   *
   * Keys of this type can be used only in the DEV life cycle state.
   */
  kSigVerifyKeyTypeDev,
} sigverify_key_type_t;

/**
 * An RSA public key stored in mask ROM.
 */
typedef struct sigverify_mask_rom_key {
  /**
   * An RSA public key.
   */
  sigverify_rsa_key_t key;
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
} sigverify_mask_rom_key_t;

/**
 * Public keys for signature verification.
 *
 * Note: Declared here to be able to use in tests.
 */
extern const sigverify_mask_rom_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys];

/**
 * Returns the key with the given ID.
 *
 * This function also checks whether the key with the given ID is valid by
 * reading the corresponding entry from the `CREATOR_SW_CFG_KEY_IS_VALID` OTP
 * item.
 *
 * @param key_id A key ID.
 * @param key Key with the given ID, valid only if it exists.
 * @return Result of the operation.
 */
rom_error_t sigverify_rsa_key_get(uint32_t key_id,
                                  const sigverify_rsa_key_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_H_
