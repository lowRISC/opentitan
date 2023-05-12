// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"

#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"
#include "sw/device/silicon_creator/lib/sigverify/mod_exp_otbn.h"

#include "otp_ctrl_regs.h"

/*
 * Shares for producing the `flash_exec` value in encoded message check. First
 * 95 shares are generated using the `sparse-fsm-encode` script while the last
 * share is `kSigverifySpxSuccess ^ kSigverifyFlashExec ^ kShares[0] ^ ... ^
 * kShares[94]` so that xor'ing all shares and `kSigverifySpxSuccess` produces
 * `kSigverifyFlashExec`, i.e. the value that unlocks flash execution.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 95 -n 32 \
 *     -s 3118901143 --language=c
 *
 * Minimum Hamming distance: 7
 * Maximum Hamming distance: 26
 * Minimum Hamming weight: 9
 * Maximum Hamming weight: 23
 */
static const uint32_t kSigverifyShares[kSigVerifyRsaNumWords] = {
    0xaf28073b, 0x5eb7dcfb, 0x177240b5, 0xa8469df3, 0x2e92e9c0, 0x83ed133b,
    0x0c9e99f0, 0x25611bd9, 0x411a9d85, 0x5c52b3df, 0x4347a537, 0x1e78e574,
    0x273e33af, 0x6f363bba, 0x11e4ee52, 0xd29ad9aa, 0x4fc2ac85, 0x52490c66,
    0x59c2528c, 0xef8d3ab2, 0xe74d7eb8, 0x2822259c, 0xe58efaa3, 0xe702fa04,
    0x82c670f6, 0x42be0a77, 0x3b021ea0, 0x09bd2a22, 0x26d656a4, 0x2f8e008f,
    0xefca5842, 0xfbc3a713, 0x4ce07aa1, 0xc1826ecc, 0xc697d53f, 0xf6a69161,
    0x4a7d7628, 0x87f2e957, 0x84db848d, 0xe05e01c5, 0x6188ff27, 0xbf1a2b31,
    0xb51d4166, 0x85fd6e7c, 0x59c5d2d5, 0x13c6e4e6, 0xff83c944, 0xc78cd4bb,
    0x8710d989, 0x7608c41e, 0x1061b036, 0x9c2fb244, 0x34a26844, 0x2bdc22a2,
    0xfd1d95f3, 0x94ac4e84, 0x1a99ce21, 0xd54eb8f7, 0x54c2cd9f, 0x70a967c8,
    0xde39d471, 0x652563cd, 0x3d4adea1, 0x1cf6631c, 0xb27d16ee, 0x3a18bafa,
    0xd8a86a86, 0xd839cd7b, 0xda2ab05a, 0x37fc1d99, 0xbc702308, 0x01d57596,
    0x480d3091, 0x51420446, 0xcc56d97c, 0x7aa57434, 0x7b6097ae, 0x45bca8ae,
    0xb0b1e322, 0x5487b90f, 0x1045e6ef, 0x87ad10f0, 0x4c72b7f0, 0xc527c9a3,
    0x29ed4350, 0xe345625b, 0x57063d83, 0xbb56900a, 0xbfb1be4c, 0x1c454e8f,
    0xdb27c1b7, 0xbe02c694, 0x2604d74a, 0x4d6516dd, 0x322918ab, 0x5f320b43,
};

/**
 * Checks the padding and the digest of an EMSA-PKCS1-v1_5 encoded message.
 *
 * EMSA-PKCS1-v1_5 is described in Section 9.2 of PKCS #1: RSA Cryptography
 * Specifications Version 2.2 (https://tools.ietf.org/html/rfc8017#section-9.2).
 * In PKCS#1, sequences are indexed from the leftmost byte and the first byte is
 * the most significant byte. An encoded message EM is an octet string of the
 * form:
 *    EM = 0x00 || 0x01 || PS || 0x00 || T, where
 * PS is a byte string of `0xff`s, T is the DER encoding of ASN.1 value of type
 * DigestInfo that contains the digest algorithm and the digest, and || denotes
 * concatenation. For SHA-256:
 *    T = (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || H,
 * where H is the digest.
 *
 * This function checks the padding and the digest of an encoded message as
 * described in PKCS#1 but works on little-endian buffers.
 *
 * @param enc_msg An encoded message, little-endian.
 * @param act_digest Actual digest of the message being verified, little-endian.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
static rom_error_t sigverify_encoded_message_check(
    sigverify_rsa_buffer_t *enc_msg, const hmac_digest_t *act_digest,
    uint32_t *flash_exec) {
  // The algorithm below uses shares, i.e. trivial secret sharing, to check an
  // encoded message and produce two values: `flash_exec` and `result`.
  // `flash_exec` is the value to write to the flash_ctrl EXEC register to
  // unlock flash execution and `result` is the return value. We produce
  // `result` in addition to `flash_exec` to avoid having the unlock value in
  // registers or memory just for checking the result of signature verification.
  // The algorithm consists of two steps:
  //
  // 1. First, we xor each word of `enc_msg` with the corresponding expected
  // value and share (`kSigverifyShares[i]`). At the end of this step, `enc_msg`
  // becomes `kSigverifyShares` if it's correct and garbage otherwise. Note
  // that this step of the algorithm is implemented using separate loops to
  // reduce stack usage.
  //
  // 2. Next, we produce `flash_exec` and `result`. `flash_exec` is produced by
  // xor'ing all words of `enc_msg` with each other. If `enc_msg` is correct,
  // `flash_exec` will be `kSigverifyFlashExec` due to the way
  // `kSigverifyShares` is defined. To make sure that we don't produce this
  // value otherwise, we compare each word of `enc_msg` with the corresponding
  // expected value and set `flash_exec` to `UINT32_MAX` at each iteration if
  // there is a mismatch. Finally, we produce the return value `result` from
  // `flash_exec` by xor'ing parts of it together. Note that the hardware
  // constant `kSigverifyFlashExec` is chosen such that this operation results
  // in `kErrorOk`.

  // Step 1: Process `enc_msg` so that it becomes `kSigverifyShares` if it's
  // correct, garbage otherwise.
  uint32_t *enc_msg_ptr = enc_msg->data;
  size_t i = 0;
  for (size_t j = 0; launder32(j) < kHmacDigestNumWords; ++j, ++i) {
    enc_msg_ptr[i] ^= act_digest->digest[j] ^ kSigverifyShares[i];
  }
  // Note: This also includes the zero byte right before PS.
  static const uint32_t kEncodedSha256[] = {
      0x05000420, 0x03040201, 0x86480165, 0x0d060960, 0x00303130,
  };
  for (size_t j = 0; launder32(j) < ARRAYSIZE(kEncodedSha256); ++j, ++i) {
    enc_msg_ptr[i] ^= kEncodedSha256[j] ^ kSigverifyShares[i];
  }
  // Note: `kPsLen` excludes the last word of `enc_msg`, which is 0x0001ffff.
  static const size_t kPsLen = ARRAYSIZE(enc_msg->data) -
                               ARRAYSIZE(kEncodedSha256) -
                               ARRAYSIZE(act_digest->digest) - /*last word*/ 1;
  // PS up to the last word.
  for (size_t j = 0; launder32(j) < kPsLen; ++j, ++i) {
    enc_msg_ptr[i] ^= 0xffffffff ^ kSigverifyShares[i];
  }
  // Last word.
  enc_msg_ptr[i] ^= 0x0001ffff ^ kSigverifyShares[i];
  HARDENED_CHECK_EQ(i, kSigVerifyRsaNumWords - 1);

  // Step 2: Reduce `enc_msg` to produce the value to write to flash_ctrl EXEC
  // register (`flash_exec`) and the return value (`result`).
  uint32_t flash_exec_rsa = 0;
  uint32_t diff = 0;
  for (i = 0; launder32(i) < kSigVerifyRsaNumWords; ++i) {
    // Following three statements set `diff` to `UINT32_MAX` if `enc_msg[i]` is
    // incorrect, no change otherwise.
    diff |= enc_msg_ptr[i] ^ kSigverifyShares[i];
    diff |= ~diff + 1;          // Set upper bits to 1 if not 0, no change o/w.
    diff |= ~(diff >> 31) + 1;  // Set to all 1s if MSB is set, no change o/w.

    flash_exec_rsa ^= enc_msg_ptr[i];
    // Set `flash_exec_rsa` to `UINT32_MAX` if `enc_msg` is incorrect.
    flash_exec_rsa |= diff;
  }
  HARDENED_CHECK_EQ(i, kSigVerifyRsaNumWords);

  // Note: `kSigverifyRsaSuccess` is defined such that the following operation
  // produces `kErrorOk`.
  rom_error_t result = sigverify_rsa_success_to_ok(flash_exec_rsa);
  *flash_exec ^= flash_exec_rsa;
  if (launder32(result) == kErrorOk) {
    HARDENED_CHECK_EQ(result, kErrorOk);
    return result;
  }

  return kErrorSigverifyBadRsaSignature;
}

/**
 * Determines whether the software implementation should be used for signature
 * verification.
 *
 * During manufacturing (TEST_UNLOCKED*), software implementation is used by
 * default since OTP may not have been programmed yet. The implementation to use
 * after manufacturing (PROD, PROD_END, DEV, RMA) is determined by the OTP
 * value.
 *
 * @param lc_state Life cycle state of the device.
 * @return Whether to use software implementation for signature verification.
 */
static hardened_bool_t sigverify_use_sw_rsa_verify(lifecycle_state_t lc_state) {
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      // Don't read from OTP during manufacturing. Use software
      // implementation by default.
      return kHardenedBoolTrue;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      return otp_read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET);
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      return otp_read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET);
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      return otp_read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET);
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return otp_read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t sigverify_rsa_verify(const sigverify_rsa_buffer_t *signature,
                                 const sigverify_rsa_key_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state,
                                 uint32_t *flash_exec) {
  hardened_bool_t use_sw = sigverify_use_sw_rsa_verify(lc_state);
  sigverify_rsa_buffer_t enc_msg;
  rom_error_t error = kErrorSigverifyBadRsaSignature;
  switch (use_sw) {
    case kHardenedBoolTrue:
      error = sigverify_mod_exp_ibex(key, signature, &enc_msg);
      break;
    case kHardenedBoolFalse:
      error = sigverify_mod_exp_otbn(key, signature, &enc_msg);
      break;
    default:
      HARDENED_TRAP();
  }
  if (launder32(error) != kErrorOk) {
    *flash_exec ^= UINT32_MAX;
    return error;
  }
  HARDENED_CHECK_EQ(error, kErrorOk);
  return sigverify_encoded_message_check(&enc_msg, act_digest, flash_exec);
}

// Extern declarations for the inline functions in the header.
extern uint32_t sigverify_rsa_success_to_ok(uint32_t v);
