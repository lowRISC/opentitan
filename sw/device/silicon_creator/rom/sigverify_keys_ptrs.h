// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_PTRS_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of RSA public keys.
   */
  kSigVerifyNumRsaKeys = 2,
  /**
   * Step size to use when checking RSA public keys.
   *
   * This must be coprime with and less than `kSigverifyNumRsaKeys`.
   * Note: Step size is not applicable when `kSigverifyNumRsaKeys` is 1.
   */
  kSigverifyRsaKeysStep = 1,
};

/**
 * Key types.
 *
 * The life cycle states in which a key can be used depend on its type.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 3 -n 32 \
 *     -s 1985033815 --language=c
 *
 * Minimum Hamming distance: 15
 * Maximum Hamming distance: 18
 * Minimum Hamming weight: 13
 * Maximum Hamming weight: 16
 */
typedef enum sigverify_key_type {
  /**
   * A key used for manufacturing, testing, and RMA.
   *
   * Keys of this type can be used only in TEST_UNLOCKED* and RMA life cycle
   * states.
   */
  kSigverifyKeyTypeTest = 0x3ff0c819,
  /**
   * A production key.
   *
   * Keys of this type can be used in all operational life cycle states, i.e.
   * states in which CPU execution is enabled.
   */
  kSigverifyKeyTypeProd = 0x43a839ad,
  /**
   * A development key.
   *
   * Keys of this type can be used only in the DEV life cycle state.
   */
  kSigverifyKeyTypeDev = 0x7a01a471,
} sigverify_key_type_t;

/**
 * An RSA public key stored in ROM.
 */
typedef struct sigverify_rom_key {
  /**
   * An RSA public key.
   */
  sigverify_rsa_key_t key;
  /**
   * Type of the key.
   */
  sigverify_key_type_t key_type;
} sigverify_rom_key_t;

/**
 * Public keys for signature verification.
 *
 * Note: Declared here to be able to use in tests.
 */
extern const sigverify_rom_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys];

#ifdef OT_PLATFORM_RV32

/**
 * Returns a pointer to the RSA public keys stored in the ROM.
 *
 * @return Pointer to the RSA public keys.
 */
inline const sigverify_rom_key_t *sigverify_rsa_keys_ptr_get(void) {
  return kSigVerifyRsaKeys;
}

/**
 * Returns the number of RSA public keys stored in the ROM.
 *
 * @return Number of RSA public keys.
 */
inline size_t sigverify_num_rsa_keys_get(void) { return kSigVerifyNumRsaKeys; }

/**
 * Returns the step size to use when checking RSA public keys.
 *
 * @return Step size that is coprime with and less than the return value of
 * `sigverify_num_rsa_keys_get()`.
 */
inline size_t sigverify_rsa_keys_step_get(void) {
  return kSigverifyRsaKeysStep;
}

#else

/**
 * Declarations for the functions above that should be defined in tests.
 */
const sigverify_rom_key_t *sigverify_rsa_keys_ptr_get(void);
size_t sigverify_num_rsa_keys_get(void);
size_t sigverify_rsa_keys_step_get(void);

#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_KEYS_PTRS_H_
