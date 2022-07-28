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
 * Possible range of instruction counts for modexp.
 *
 * This range should represent the theoretical minimum/maximum instruction
 * counts for any input to the program; if the instruction count recorded by
 * OTBN is different, we will suspect a fault injection attack.
 *
 * The OTBN modexp implementation is not constant-time, but that is okay
 * because it has no secret inputs and therefore can't leak secret information.
 *
 * IMPORTANT: This may need to be modified if the modexp routine is changed! If
 * updating this value, please both use the automatic script
 * (get_instruction_count_range.py) and also double-check by manually
 * modifying the code to skip/take all branches.
 */
enum {
  kModExpOtbnInsnCountMin = 181147,
  kModExpOtbnInsnCountMax = 198397,
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
