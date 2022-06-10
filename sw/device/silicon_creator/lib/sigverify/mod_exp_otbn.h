// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_OTBN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_OTBN_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Manually-calculated instruction count range.
 *
 * The OTBN modexp implementation is not constant-time (which is okay because
 * it has no secret inputs). However, all valid control-flow paths should fall
 * within this range, which is calculated by changing the code to either take
 * all branches or skip them all.
 *
 * IMPORTANT: This may need to be modified if the modexp routine is changed!
 */
enum {
  kModExpOtbnInsnCountMin = 182578,
  kModExpOtbnInsnCountMax = 197207,
};

/**
 * Computes the modular exponentiation of an RSA signature on OTBN.
 *
 * Given an RSA public key and sig, this function computes sig^e mod n using
 * Montgomery multiplication, where
 * - sig is an RSA signature,
 * - e and n are the exponent and the modulus of the key, respectively.
 *
 * The key exponent is always 65537; no other exponents are supported.
 *
 * @param key An RSA public key.
 * @param sig Buffer that holds the signature, little-endian.
 * @param result Buffer to write the result to, little-endian.
 * @return The result of the operation.
 */
rom_error_t sigverify_mod_exp_otbn(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_OTBN_H_
