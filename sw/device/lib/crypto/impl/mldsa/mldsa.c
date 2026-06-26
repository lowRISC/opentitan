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

// OTBN app.
OTBN_DECLARE_APP_SYMBOLS(mldsa87_verify);
// Inputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_pk);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_sig);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_mu);
// Outputs.
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_res_ok);
OTBN_DECLARE_SYMBOL_ADDR(mldsa87_verify, mldsa87_verify_res_c_tilde_prime);

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

  return otbn_dmem_sec_wipe();
}
