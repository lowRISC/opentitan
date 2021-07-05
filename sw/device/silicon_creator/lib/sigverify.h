// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Gets the ID of an RSA public key from its modulus.
 *
 * ID of a key is the least significant word of its modulus.
 * Callers must make sure that `modulus` is valid before calling this function.
 *
 * @param key An RSA public key.
 * @return ID of the key.
 */
inline uint32_t sigverify_rsa_key_id_get(
    const sigverify_rsa_buffer_t *modulus) {
  return modulus->data[0];
}

/**
 * Verifies an RSASSA-PKCS1-v1_5 signature.
 *
 * @param signed_message Message whose signature is to be verified.
 * @param signed_message_len Length of the signed message in bytes.
 * @param signature Signature to be verified.
 * @param key Signer's RSA public key.
 * @return Result of the operation.
 */
rom_error_t sigverify_rsa_verify(const void *signed_message,
                                 size_t signed_message_len,
                                 const sigverify_rsa_buffer_t *signature,
                                 const sigverify_rsa_key_t *key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_H_
