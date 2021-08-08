// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_PTRS_H_

#include <stddef.h>

#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of RSA public keys.
   */
  kSigVerifyNumRsaKeys = 2,
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
  kSigverifyKeyTypeDev,
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

#ifndef OT_OFF_TARGET_TEST

/**
 * Returns a pointer to the RSA public keys stored in the Mask ROM.
 *
 * @return Pointer to the RSA public keys.
 */
inline const sigverify_mask_rom_key_t *sigverify_rsa_keys_ptr_get(void) {
  return kSigVerifyRsaKeys;
}

/**
 * Returns the number of RSA public keys stored in the Mask ROM.
 *
 * @return Number of RSA public keys.
 */
inline size_t sigverify_num_rsa_keys_get(void) { return kSigVerifyNumRsaKeys; }

#else

/**
 * Declarations for the functions above that should be defined in tests.
 */
const sigverify_mask_rom_key_t *sigverify_rsa_keys_ptr_get(void);
size_t sigverify_num_rsa_keys_get(void);

#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_KEYS_PTRS_H_
