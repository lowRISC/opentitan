// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/curve25519.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', '2', 'r')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_curve25519);  // The OTBN 25519 app.
static const otbn_app_t kOtbnAppCurve25519 = OTBN_APP_T_INIT(run_curve25519);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, mode);  // Mode of operation.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_verify_result);  // Verification result.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_sig_R);  // Signature commitment R.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_sig_S);  // Signature response S.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_public_key);  // Public Key A.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_hash_k);  // Challenge hash k.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, ed25519_verify_lhs);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, ed25519_verify_rhs);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_s0);  // 384-bit first share of s.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_s1);  // 384-bit second shares of s.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_r0);  // 640-bit first share of r.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         ed25519_r1);  // 640-bit second share of r.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         x25519_private_key);  // X25519 private key.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         x25519_public_key);  // X25519 public key.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519,
                         x25519_shared_key);  // X25519 shared key.

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_curve25519, mode);
static const otbn_addr_t kOtbnVarVerifyRes =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_verify_result);
static const otbn_addr_t kOtbnVarSigR =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_sig_R);
static const otbn_addr_t kOtbnVarSigS =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_sig_S);
static const otbn_addr_t kOtbnVarPubKey =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_public_key);
static const otbn_addr_t kOtbnVarHashK =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_hash_k);
static const otbn_addr_t kOtbnVarVerifyLhs =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_verify_lhs);
static const otbn_addr_t kOtbnVarVerifyRhs =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_verify_rhs);
static const otbn_addr_t kOtbnVarS0 =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_s0);
static const otbn_addr_t kOtbnVarS1 =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_s1);
static const otbn_addr_t kOtbnVarR0 =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_r0);
static const otbn_addr_t kOtbnVarR1 =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_r1);
static const otbn_addr_t kOtbnVarX25519PrivateKey =
    OTBN_ADDR_T_INIT(run_curve25519, x25519_private_key);
static const otbn_addr_t kOtbnVarX25519PublicKey =
    OTBN_ADDR_T_INIT(run_curve25519, x25519_public_key);
static const otbn_addr_t kOtbnVarX25519SharedKey =
    OTBN_ADDR_T_INIT(run_curve25519, x25519_shared_key);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_SIGN_STAGE1);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_SIGN_STAGE2);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_X25519);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_X25519_KEYGEN);

static const uint32_t kOtbnCurve25519ModeKeygen =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_KEYGEN);
static const uint32_t kOtbnCurve25519ModeSignStage1 =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_SIGN_STAGE1);
static const uint32_t kOtbnCurve25519ModeSignStage2 =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_SIGN_STAGE2);
static const uint32_t kOtbnCurve25519ModeVerify =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_VERIFY);
static const uint32_t kOtbnCurve25519ModeX25519 =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_X25519);
static const uint32_t kOtbnCurve25519ModeX25519Keygen =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_X25519_KEYGEN);

enum {
  /*
   * The expected instruction counts for constant time functions.
   */
  kModeKeygenInsCnt = 339495,
  kModeSignStage1InsCnt = 679051,
  kModeSignStage2InsCnt = 655,
};

/**
 * Write a masked scalar to DMEM.
 *
 * This routine can be used for both s and r by passing the shares directly to
 * this function and setting `share_len` accordingly.
 *
 * @param share0 The first share of the scalar.
 * @param share1 The second share of the scalar.
 * @param share_len The size of the scalar shares in number of 32-bit words.
 * @param share0_addr The DMEM address of the first share.
 * @param share1_addr The DMEM address of the second share.
 * @return OK.
 */
static status_t curve25519_masked_scalar_write(const uint32_t *share0,
                                               const uint32_t *share1,
                                               size_t share_len,
                                               const otbn_addr_t share0_addr,
                                               const otbn_addr_t share1_addr) {
  HARDENED_TRY(otbn_dmem_write(share_len, share0, share0_addr));
  HARDENED_TRY(otbn_dmem_write(share_len, share1, share1_addr));

  // Write trailing 0s so that OTBN's 256-bit read of the shares does not cause
  // an error.
  HARDENED_TRY(otbn_dmem_set(kCurve25519MaskedScalarPaddingWords, 0,
                             share0_addr + (share_len << 2)));
  HARDENED_TRY(otbn_dmem_set(kCurve25519MaskedScalarPaddingWords, 0,
                             share1_addr + (share_len << 2)));

  return OTCRYPTO_OK;
}

status_t curve25519_keygen_start(const curve25519_masked_scalar_s_t *s) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into keygen.
  uint32_t mode = kOtbnCurve25519ModeKeygen;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Write the shares of s to DMEM.
  HARDENED_TRY(curve25519_masked_scalar_write(s->share0, s->share1,
                                              kCurve25519MaskedScalarSWords,
                                              kOtbnVarS0, kOtbnVarS1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_keygen_finalize(
    uint32_t public_key[kCurve25519PointWords]) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeKeygenInsCnt);

  // Read the public key A from OTBN dmem.
  HARDENED_TRY(
      otbn_dmem_read(kCurve25519PointWords, kOtbnVarPubKey, public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_sign_stage1_start(const curve25519_masked_scalar_r_t *r,
                                      const curve25519_masked_scalar_s_t *s) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into stage 1 of signing.
  uint32_t mode = kOtbnCurve25519ModeSignStage1;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Write the shares of r and s to DMEM.
  HARDENED_TRY(curve25519_masked_scalar_write(r->share0, r->share1,
                                              kCurve25519MaskedScalarRWords,
                                              kOtbnVarR0, kOtbnVarR1));
  HARDENED_TRY(curve25519_masked_scalar_write(s->share0, s->share1,
                                              kCurve25519MaskedScalarSWords,
                                              kOtbnVarS0, kOtbnVarS1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_sign_stage1_finalize(
    curve25519_signature_t *sig, uint32_t public_key[kCurve25519PointWords]) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeSignStage1InsCnt);

  // Read the signature commitment R from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kCurve25519PointWords, kOtbnVarSigR, sig->r));

  // Read the public key A from OTBN dmem.
  HARDENED_TRY(
      otbn_dmem_read(kCurve25519PointWords, kOtbnVarPubKey, public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_sign_stage2_start(
    const uint32_t hash_k[kCurve25519HashWords],
    const curve25519_masked_scalar_r_t *r,
    const curve25519_masked_scalar_s_t *s) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into stage 2 of signing.
  uint32_t mode = kOtbnCurve25519ModeSignStage2;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Set challenge hash k.
  HARDENED_TRY(otbn_dmem_write(kCurve25519HashWords, hash_k, kOtbnVarHashK));

  // Write the shares of r and s to DMEM.
  HARDENED_TRY(curve25519_masked_scalar_write(r->share0, r->share1,
                                              kCurve25519MaskedScalarRWords,
                                              kOtbnVarR0, kOtbnVarR1));
  HARDENED_TRY(curve25519_masked_scalar_write(s->share0, s->share1,
                                              kCurve25519MaskedScalarSWords,
                                              kOtbnVarS0, kOtbnVarS1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_sign_stage2_finalize(curve25519_signature_t *sig) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeSignStage2InsCnt);

  // Read the signature response S from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kCurve25519ScalarWords, kOtbnVarSigS, sig->s));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_verify_start(
    const uint32_t hash_k[kCurve25519HashWords], curve25519_signature_t *sig,
    const uint32_t public_key[kCurve25519PointWords]) {
  // Load the Curve25519 app and set up data pointers
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into verifying.
  uint32_t mode = kOtbnCurve25519ModeVerify;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Set challenge hash k.
  HARDENED_TRY(otbn_dmem_write(kCurve25519HashWords, hash_k, kOtbnVarHashK));

  // Set the signature commitment R.
  HARDENED_TRY(otbn_dmem_write(kCurve25519PointWords, sig->r, kOtbnVarSigR));

  // Set the signature response S.
  HARDENED_TRY(otbn_dmem_write(kCurve25519ScalarWords, sig->s, kOtbnVarSigS));

  // Set the public key.
  HARDENED_TRY(
      otbn_dmem_write(kCurve25519PointWords, public_key, kOtbnVarPubKey));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_verify_finalize(hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarVerifyRes, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read the computed LHS and RHS out of OTBN dmem.
  uint32_t lhs[kCurve25519PointWords];
  uint32_t rhs[kCurve25519PointWords];
  HARDENED_TRY(otbn_dmem_read(kCurve25519PointWords, kOtbnVarVerifyLhs, lhs));
  HARDENED_TRY(otbn_dmem_read(kCurve25519PointWords, kOtbnVarVerifyRhs, rhs));

  *result = hardened_memeq(lhs, rhs, kCurve25519PointWords);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_x25519_start(
    const uint32_t private_key[kCurve25519ScalarWords],
    const uint32_t public_key[kCurve25519PointWords]) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into x25519.
  uint32_t mode = kOtbnCurve25519ModeX25519;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Write the private key to DMEM.
  HARDENED_TRY(otbn_dmem_write(kCurve25519ScalarWords, private_key,
                               kOtbnVarX25519PrivateKey));

  // Write the public key to DMEM.
  HARDENED_TRY(otbn_dmem_write(kCurve25519PointWords, public_key,
                               kOtbnVarX25519PublicKey));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_x25519_finalize(
    uint32_t shared_secret[kCurve25519PointWords]) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the shared secret from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kCurve25519PointWords, kOtbnVarX25519SharedKey,
                              shared_secret));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_x25519_keygen_start(
    const uint32_t private_key[kCurve25519ScalarWords]) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into x25519_keygen.
  uint32_t mode = kOtbnCurve25519ModeX25519Keygen;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Write the private key to DMEM.
  HARDENED_TRY(otbn_dmem_write(kCurve25519ScalarWords, private_key,
                               kOtbnVarX25519PrivateKey));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_x25519_keygen_finalize(
    uint32_t public_key[kCurve25519PointWords]) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kCurve25519PointWords, kOtbnVarX25519PublicKey,
                              public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}
