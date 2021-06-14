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
};

/**
 * Public keys for signature verification.
 *
 * Note: Declared here to be able to use in tests.
 */
extern const sigverify_rsa_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys];

/**
 * Returns the key with the given ID.
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
