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
OTBN_DECLARE_SYMBOL_ADDR(
    run_curve25519,
    ed25519_hash_h_low);  // 32 lowest bytes of the key hash.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, ed25519_hash_r);  // Message hash r.

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
static const otbn_addr_t kOtbnVarHashHlow =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_hash_h_low);
static const otbn_addr_t kOtbnVarHashR =
    OTBN_ADDR_T_INIT(run_curve25519, ed25519_hash_r);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_SIGN_STAGE1);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_SIGN_STAGE2);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_VERIFY);

static const uint32_t kOtbnCurve25519ModeSignStage1 =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_SIGN_STAGE1);
static const uint32_t kOtbnCurve25519ModeSignStage2 =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_SIGN_STAGE2);
static const uint32_t kOtbnCurve25519ModeVerify =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_VERIFY);

status_t curve25519_sign_stage1_start(
    const uint32_t hash_r[kCurve25519HashWords],
    const uint32_t hash_h_low[kCurve25519HalfHashWords]) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into stage 1 of signing.
  uint32_t mode = kOtbnCurve25519ModeSignStage1;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Set 64 Byte hash r.
  HARDENED_TRY(otbn_dmem_write(kCurve25519HashWords, hash_r, kOtbnVarHashR));

  // Set lower 32 bytes of private key hash h.
  HARDENED_TRY(
      otbn_dmem_write(kCurve25519HalfHashWords, hash_h_low, kOtbnVarHashHlow));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_sign_stage1_finalize(
    curve25519_signature_t *sig, uint32_t public_key[kCurve25519PointWords]) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  // Read the signature commitment R from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kCurve25519PointWords, kOtbnVarSigR, sig->r));

  // Read the public key A from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kCurve25519PointWords, kOtbnVarPubKey, public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t curve25519_sign_stage2_start(
    const uint32_t hash_k[kCurve25519HashWords],
    const uint32_t hash_r[kCurve25519HashWords],
    const uint32_t hash_h_low[kCurve25519HalfHashWords]) {
  // Load the Curve25519 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppCurve25519));

  // Set mode so start() will jump into stage 2 of signing.
  uint32_t mode = kOtbnCurve25519ModeSignStage2;
  HARDENED_TRY(otbn_dmem_write(kCurve25519ModeWords, &mode, kOtbnVarMode));

  // Set challenge hash k.
  HARDENED_TRY(otbn_dmem_write(kCurve25519HashWords, hash_k, kOtbnVarHashK));

  // Set 64 Byte hash r.
  HARDENED_TRY(otbn_dmem_write(kCurve25519HashWords, hash_r, kOtbnVarHashR));

  // Set lower half of precomputed secret key hash h.
  HARDENED_TRY(
      otbn_dmem_write(kCurve25519HalfHashWords, hash_h_low, kOtbnVarHashHlow));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t curve25519_sign_stage2_finalize(curve25519_signature_t *sig) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  // Read the signature response S from OTBN dmem.
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kCurve25519ScalarWords, kOtbnVarSigS, sig->s));

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
  HARDENED_TRY_WIPE_DMEM(otbn_busy_wait_for_done());

  uint32_t resp;
  uint32_t expected_resp = kCurve25519VerifySuccess;
  HARDENED_TRY_WIPE_DMEM(
      otbn_dmem_read(kCurve25519ResultWords, kOtbnVarVerifyRes, &resp));
  *result = hardened_memeq(&resp, &expected_resp, kCurve25519ResultWords);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}
