// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/silicon_creator/mask_rom/sig_verify_keys.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// FIXME: Make static and move this comment to the source file. This is here
// just to be able to add a simple test.
/**
 * Computes the Montgomery reduction of the product of two integers.
 *
 * Given an RSA public key, x, and y this function computes x*y*R^-1 mod n,
 * where
 * - x and y are integers with `kSigVerifyRsaNumWords` base 2^32 digits,
 * - n is the modulus of the key, and
 * - R is 2^`kSigVerifyRsaNumBits`, e.g. 2^3072 for RSA-3072.
 *
 * See Handbook of Applied Cryptography, Ch. 14, Alg. 14.36.
 *
 * @param key An RSA public key.
 * @param x Buffer that holds `x`, little-endian.
 * @param y Buffer that holds `y`, little-endian.
 * @param[out] result Buffer to write the result to, little-endian.
 */
void mont_mul(const sigverify_rsa_key_t *key, const sigverify_rsa_buffer_t *x,
              const sigverify_rsa_buffer_t *y, sigverify_rsa_buffer_t *result);

/**
 * Computes the modular exponentiation of an RSA signature.
 *
 * Given an RSA public key and sig, this function computes sig^e mod n using
 * Montgomery multiplication, where
 * - sig is an RSA signature,
 * - e and n are the exponent and the modulus of the key, respectively.
 *
 * @param key An RSA public key.
 * @param sig Buffer that holds the signature, little-endian.
 * @param result Buffer to write the result to, little-endian.
 * @return True if successful, false otherwise.
 */
// FIXME: Error codes are still under discussion, update after we reach a
// decision.
bool sigverify_mod_exp_ibex(const sigverify_rsa_key_t *key,
                            const sigverify_rsa_buffer_t *sig,
                            sigverify_rsa_buffer_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_RSA_VERIFY_H_
