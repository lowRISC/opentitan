// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/sigverify/ecdsa_p256_verify.h"

#include "sw/lib/sw/device/silicon_creator/attestation.h"
#include "sw/lib/sw/device/silicon_creator/otbn_boot_services.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/ecdsa_p256_key.h"

#include "otp_ctrl_regs.h"

enum {
  kP256SignatureWords = kP256PublicKeyWords,
  kP256SignatureCordWords = kP256SignatureWords / 2,
};

/*
 * Shares for producing the `kSigverifyEcdsaSuccess` value in
 * `sigverify_encoded_message_check)`. First 7 shares are generated using the
 * `sparse-fsm-encode` script while the last share is `kSigverifySpxSuccess ^
 * kSigverifyFlashExec ^ kShares[0] ^ ... ^ kShares[6]` ==
 * `kSigverifyEcdsaSuccess`.
 *
 * It follows that:
 *
 * `kSigverifyFlashExec = kSigverifyEcdsaSuccess ^ kSigverifySpxSuccess`
 *
 * Where `kSigverifyFlashExec` is the value to write to the flash_ctrl to enable
 * code execution.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 7 -n 32 \
 *     -s 3118901143 --language=c
 *
 * Minimum Hamming distance: 9
 * Maximum Hamming distance: 25
 * Minimum Hamming weight: 14
 * Maximum Hamming weight: 23
 */
static const uint32_t kSigverifyShares[kP256SignatureCordWords] = {
    0xaf28073b, 0x5eb7dcfb, 0x177240b5, 0xa8469df3,
    0x2e92e9c0, 0x83ed133b, 0x0c9e99f0, 0xc04cd16d,
};

/**
 * Checks the encoded message and produces the value to write to the flash_ctrl.
 *
 * @param recovered_r Recovered r parameter, little-endian.
 * @param signature Provided signature, little-endian.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t sigverify_encoded_message_check(
    sigverify_ecdsa_p256_buffer_t *recovered_r,
    const sigverify_ecdsa_p256_buffer_t *signature, uint32_t *flash_exec) {
  // The algorithm below uses shares, i.e. trivial secret sharing, to check an
  // encoded message and produce two values: `flash_exec` and `result`.
  // `flash_exec` is the value to write to the flash_ctrl EXEC register to
  // unlock flash execution and `result` is the return value. We produce
  // `result` in addition to `flash_exec` to avoid having the unlock value in
  // registers or memory just for checking the result of signature verification.
  // The algorithm consists of two steps:
  //
  // 1. First, we xor each word of `recovered_r` with the corresponding expected
  // value and share (`kSigverifyShares[i]`). At the end of this step,
  // `recovered_r` becomes `kSigverifyShares` if it's correct and garbage
  // otherwise.
  //
  // 2. Next, we produce `flash_exec` and `result`. `flash_exec` is produced by
  // xor'ing all words of `recovered_r` with each other. If `recovered_r` is
  // correct, `flash_exec` will be `kSigverifyEcdsaSuccess` due to the way
  // `kSigverifyShares` is defined. To make sure that we don't produce this
  // value otherwise, we compare each word of `recovered_r` with the
  // corresponding expected value and set `flash_exec` to `UINT32_MAX` at each
  // iteration if there is a mismatch. Finally, we produce the return value
  // `result` from `flash_exec` by xor'ing parts of it together. Note that the
  // hardware constant `kSigverifyEcdsaSuccess` is chosen such that this
  // operation results in `kErrorOk`.

  // Step 1: Process `recovered_r` so that it becomes `kSigverifyShares` if it's
  // correct, garbage otherwise.
  uint32_t *recovered_r_ptr = recovered_r->data;
  size_t i = 0;
  for (size_t j = 0; launder32(j) < kP256SignatureCordWords; ++j, ++i) {
    recovered_r_ptr[i] ^= signature->data[j] ^ kSigverifyShares[i];
  }
  HARDENED_CHECK_EQ(i, kP256SignatureCordWords);

  // Step 2: Reduce `recovered_r` to produce the value to write to flash_ctrl
  // EXEC register (`flash_exec`) and the return value (`result`).
  uint32_t flash_exec_ecdsa = 0;
  uint32_t diff = 0;
  for (i = 0; launder32(i) < kP256SignatureCordWords; ++i) {
    // Following three statements set `diff` to `UINT32_MAX` if `recovered_r[i]`
    // is incorrect, no change otherwise.
    diff |= recovered_r_ptr[i] ^ kSigverifyShares[i];
    diff |= ~diff + 1;          // Set upper bits to 1 if not 0, no change o/w.
    diff |= ~(diff >> 31) + 1;  // Set to all 1s if MSB is set, no change o/w.

    flash_exec_ecdsa ^= recovered_r_ptr[i];
    // Set `flash_exec_ecdsa` to `UINT32_MAX` if `recovered_r` is incorrect.
    flash_exec_ecdsa |= diff;
  }
  HARDENED_CHECK_EQ(i, kP256SignatureCordWords);

  // Note: `kSigverifyEcdsaSuccess` is defined such that the following operation
  // produces `kErrorOk`.
  rom_error_t result = sigverify_ecdsa_p256_success_to_ok(flash_exec_ecdsa);
  *flash_exec ^= flash_exec_ecdsa;
  if (launder32(result) == kErrorOk) {
    HARDENED_CHECK_EQ(result, kErrorOk);
    return result;
  }

  return kErrorSigverifyBadEcdsaSignature;
}

rom_error_t sigverify_ecdsa_p256_verify(
    const sigverify_ecdsa_p256_buffer_t *signature,
    const sigverify_ecdsa_p256_buffer_t *key, const hmac_digest_t *act_digest,
    uint32_t *flash_exec) {
  // TODO(#22134): Unify key and signature structures.
  static_assert(
      sizeof(sigverify_ecdsa_p256_buffer_t) == sizeof(attestation_public_key_t),
      "Size of sigverify_ecdsa_p256_buffer_t and attestation_public_key_t must "
      "match");
  static_assert(
      sizeof(sigverify_ecdsa_p256_buffer_t) == sizeof(attestation_signature_t),
      "Size of sigverify_ecdsa_p256_buffer_t and attestation_signature_t must "
      "match");

  sigverify_ecdsa_p256_buffer_t recovered_r;
  rom_error_t error =
      otbn_boot_sigverify((const attestation_public_key_t *)key,
                          (const attestation_signature_t *)signature,
                          act_digest, (uint32_t *)&recovered_r);
  if (launder32(error) != kErrorOk) {
    *flash_exec ^= UINT32_MAX;
    return error;
  }
  HARDENED_CHECK_EQ(error, kErrorOk);
  return sigverify_encoded_message_check(&recovered_r, signature, flash_exec);
}

// Extern declarations for the inline functions in the header.
extern uint32_t sigverify_ecdsa_p256_success_to_ok(uint32_t v);
