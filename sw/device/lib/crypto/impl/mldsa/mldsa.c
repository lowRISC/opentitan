// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'l', 'd')

// Sign app.
OTBN_DECLARE_APP_SYMBOLS(mldsa87_sign);
// Inputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_mode);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_sk);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_mu);
// Outputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_sig_c_tilde);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_sig_z);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_sign, mldsa87_sign_sig_h);

// Verify app.
OTBN_DECLARE_APP_SYMBOLS(mldsa87_verify);
// Inputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_pk);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_sig);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_mu);
// Outputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_res_ok);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_res_c_tilde_prime);

enum {
  kMldsa87AbridgedMode = 0x29d8e5c9,
};

static status_t read_signature(uint32_t *sig) {
  // Read c_tilde_prime.
  const otbn_addr_t kOtbnCTilde =
      OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_sig_c_tilde);
  HARDENED_TRY(otbn_dmem_read(kMldsa87CTildeWords, kOtbnCTilde, sig));

  // Read Z.
  const otbn_addr_t kOtbnZ = OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_sig_z);
  HARDENED_TRY(
      otbn_dmem_read(kMldsa87ZWords, kOtbnZ, sig + kMldsa87CTildeWords));

  // Read hint.
  const otbn_addr_t kOtbnH = OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_sig_h);
  HARDENED_TRY(otbn_dmem_read(kMldsa87HWords, kOtbnH,
                              sig + kMldsa87CTildeWords + kMldsa87ZWords));

  // Clear the Z vector.
  HARDENED_TRY(otbn_dmem_set(kMldsa87ZWords, 0, kOtbnZ));

  return OTCRYPTO_OK;
}

status_t mldsa87_sign_internal_start(const otcrypto_blinded_key_t *secret_key,
                                     const otcrypto_hash_digest_t *mu,
                                     uint32_t mode) {
  // Load the ML-DSA-87 sign app and write the inputs.
  const otbn_app_t kOtbnAppMldsa87Sign = OTBN_APP_T_INIT(mldsa87_sign);
  HARDENED_TRY(otbn_load_app(kOtbnAppMldsa87Sign));

  const otbn_addr_t kOtbnMode =
      OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnMode));

  const otbn_addr_t kOtbnSk = OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_sk);
  HARDENED_TRY(otbn_dmem_write(secret_key->keyblob_length / sizeof(uint32_t),
                               secret_key->keyblob, kOtbnSk));

  const otbn_addr_t kOtbnMu = OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_mu);
  HARDENED_TRY(otbn_dmem_write(mu->len, mu->data, kOtbnMu));

  return otbn_execute();
}

status_t mldsa87_sign_internal_finalize(otcrypto_word32_buf_t *signature,
                                        mldsa_sign_redundancy_t redundancy) {
  // Stall until the OTBN finishes.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read back the signature.
  HARDENED_TRY(read_signature(signature->data));

  // Return if single-sign redundancy is selected.
  if (redundancy == kMldsa87SingleSign) {
    HARDENED_CHECK_EQ(redundancy, kMldsa87SingleSign);
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_EQ(redundancy, kMldsa87DoubleSign);

  /*
   * To thwart FI attacks, we execute a second sign operation in abridged mode
   * without clearing the secret key, nonce KAPPA, RND and RHO_PRIME. After
   * the completion of the second sign the entire DMEM is wiped.
   */

  uint32_t mode = kMldsa87AbridgedMode;
  const otbn_addr_t kOtbnMode =
      OTBN_ADDR_T_INIT(mldsa87_sign, mldsa87_sign_mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnMode));

  // Buffer for the second signature value.
  uint32_t sig_cmp_data[kMldsa87SigWords];

  // Execute the second abridged sign and wait for its completion.
  HARDENED_TRY(otbn_execute());
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read back the second signature.
  HARDENED_TRY(read_signature(sig_cmp_data));

  // Make sure both signature values are equal.
  if (hardened_memeq(signature->data, sig_cmp_data, kMldsa87SigWords) !=
      kHardenedBoolTrue) {
    HARDENED_TRAP();
  }
  HARDENED_CHECK_EQ(
      hardened_memeq(signature->data, sig_cmp_data, kMldsa87SigWords),
      kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

status_t mldsa87_verify_internal_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *signature,
    const otcrypto_hash_digest_t *mu) {
  // Load the ML-DSA-87 verification app and write the inputs.
  const otbn_app_t kOtbnAppMldsa87Verify = OTBN_APP_T_INIT(mldsa87_verify);
  HARDENED_TRY(otbn_load_app(kOtbnAppMldsa87Verify));

  const otbn_addr_t kOtbnPk =
      OTBN_ADDR_T_INIT(mldsa87_verify, mldsa87_verify_pk);
  HARDENED_TRY(otbn_dmem_write(public_key->key_length / sizeof(uint32_t),
                               public_key->key, kOtbnPk));

  const otbn_addr_t kOtbnSig =
      OTBN_ADDR_T_INIT(mldsa87_verify, mldsa87_verify_sig);
  HARDENED_TRY(otbn_dmem_write(signature->len, signature->data, kOtbnSig));

  const otbn_addr_t kOtbnMu =
      OTBN_ADDR_T_INIT(mldsa87_verify, mldsa87_verify_mu);
  HARDENED_TRY(otbn_dmem_write(mu->len, mu->data, kOtbnMu));

  return otbn_execute();
}

status_t mldsa87_verify_internal_finalize(
    const otcrypto_const_word32_buf_t *signature, hardened_bool_t *result) {
  // Stall until the OTBN finishes.
  HARDENED_TRY(otbn_busy_wait_for_done());

  *result = kHardenedBoolFalse;

  // Load the status flag and make sure no error has been thrown by the app.
  uint32_t ok;
  const otbn_addr_t kOtbnOk =
      OTBN_ADDR_T_INIT(mldsa87_verify, mldsa87_verify_res_ok);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnOk, &ok));
  if (launder32(ok) != kMldsa87StatusOk) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kMldsa87StatusOk);

  // Load c_tilde_prime and compare it against the signature.
  uint32_t c_tilde_prime[kMldsa87CTildePrimeWords];
  const otbn_addr_t kOtbnCTildePrime =
      OTBN_ADDR_T_INIT(mldsa87_verify, mldsa87_verify_res_c_tilde_prime);
  HARDENED_TRY(otbn_dmem_read(kMldsa87CTildePrimeWords, kOtbnCTildePrime,
                              c_tilde_prime));

  *result =
      hardened_memeq(signature->data, c_tilde_prime, kMldsa87CTildePrimeWords);

  return OTCRYPTO_OK;
}
