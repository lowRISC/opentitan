// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/mlkem/mlkem.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'l', 'k')

// Keygen app.
OTBN_DECLARE_APP_SYMBOLS(mlkem1024_keygen);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_mode);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_seed_d_share0);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_seed_d_share1);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_seed_z_share0);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_pk_t);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_pk_rho);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_sk_s);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_sk_pk_t);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_sk_pk_rho);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_sk_hpk);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_keygen, mlkem1024_keygen_sk_z);

// Encaps app.
OTBN_DECLARE_APP_SYMBOLS(mlkem1024_encaps);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_pk_t);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_pk_rho);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_m);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_ct_u);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_ct_v);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_encaps, mlkem1024_encaps_ss);

// Decaps app.
OTBN_DECLARE_APP_SYMBOLS(mlkem1024_decaps);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_ct_u);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_ct_v);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_sk_s);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_sk_pk_t);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_sk_pk_rho);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_sk_hpk);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_sk_z);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_ss);
OTBN_DECLARE_SYMBOL_ADDR(mlkem1024_decaps, mlkem1024_decaps_seed_buf);

enum {
  kMlkem1024PkTWords = 1536 / sizeof(uint32_t),
  kMlkem1024PkRhoWords = 32 / sizeof(uint32_t),
  kMlkem1024SkSWords = 1536 / sizeof(uint32_t),
  kMlkem1024SkHpkWords = 32 / sizeof(uint32_t),
  kMlkem1024SkZWords = 32 / sizeof(uint32_t),

  kMlkem1024CtUWords = 1408 / sizeof(uint32_t),
  kMlkem1024CtVWords = 160 / sizeof(uint32_t),
  kMlkem1024SeedWords = 32 / sizeof(uint32_t),
};

status_t mlkem1024_keygen_internal_start(void) {
  // Securely wipe DMEM to initialize hardware SRAM ECC parity.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  // Load the ML-KEM-1024 keygen app.
  const otbn_app_t kOtbnAppMlkem1024Keygen = OTBN_APP_T_INIT(mlkem1024_keygen);
  HARDENED_TRY(otbn_load_app(kOtbnAppMlkem1024Keygen));

  // Write random mode flag to DMEM.
  uint32_t mode = kMlkem1024KeygenRndMode;
  const otbn_addr_t kOtbnMode =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnMode));

  return otbn_execute();
}

status_t mlkem1024_det_keygen_internal_start(
    const otcrypto_blinded_key_t *d, const otcrypto_const_word32_buf_t *z) {
  // Load the ML-KEM-1024 keygen app.
  const otbn_app_t kOtbnAppMlkem1024Keygen = OTBN_APP_T_INIT(mlkem1024_keygen);
  HARDENED_TRY(otbn_load_app(kOtbnAppMlkem1024Keygen));

  // Write deterministic mode flag to DMEM.
  uint32_t mode = kMlkem1024KeygenDetMode;
  const otbn_addr_t kOtbnMode =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_mode);
  HARDENED_TRY(otbn_dmem_write(1, &mode, kOtbnMode));

  // Write seed d shares (64 bytes total, zero-extended to 64B each for SRAM
  // ECC).
  uint32_t d_share0[16] = {0};
  uint32_t d_share1[16] = {0};
  memcpy(d_share0, d->keyblob, 32);
  memcpy(d_share1, (const uint32_t *)d->keyblob + kMlkem1024SeedWords, 32);

  const otbn_addr_t kOtbnDShare0 =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_seed_d_share0);
  HARDENED_TRY(otbn_dmem_write(16, d_share0, kOtbnDShare0));

  const otbn_addr_t kOtbnDShare1 =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_seed_d_share1);
  HARDENED_TRY(otbn_dmem_write(16, d_share1, kOtbnDShare1));

  // Write seed z_share0 (32 bytes) and z_share1 (32 zero bytes).
  const otbn_addr_t kOtbnZ0 =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_seed_z_share0);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024SeedWords, z->data, kOtbnZ0));

  uint32_t z_share1[8] = {0};
  const otbn_addr_t kOtbnZ1 =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_seed_z_share1);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024SeedWords, z_share1, kOtbnZ1));

  return otbn_execute();
}

status_t mlkem1024_keygen_internal_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key) {
  // Stall until OTBN finishes.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read public key components (pk_t: 1536 bytes, pk_rho: 32 bytes).
  const otbn_addr_t kOtbnPkT =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_pk_t);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024PkTWords, kOtbnPkT, public_key->key));

  const otbn_addr_t kOtbnPkRho =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_pk_rho);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024PkRhoWords, kOtbnPkRho,
                              public_key->key + kMlkem1024PkTWords));

  // Read secret key components (s: 1536, pk_t: 1536, pk_rho: 32, hpk: 32, z:
  // 32).
  const otbn_addr_t kOtbnSkS =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_sk_s);
  HARDENED_TRY(
      otbn_dmem_read(kMlkem1024SkSWords, kOtbnSkS, secret_key->keyblob));

  const otbn_addr_t kOtbnSkPkT =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_sk_pk_t);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024PkTWords, kOtbnSkPkT,
                              secret_key->keyblob + kMlkem1024SkSWords));

  const otbn_addr_t kOtbnSkPkRho =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_sk_pk_rho);
  HARDENED_TRY(otbn_dmem_read(
      kMlkem1024PkRhoWords, kOtbnSkPkRho,
      secret_key->keyblob + kMlkem1024SkSWords + kMlkem1024PkTWords));

  const otbn_addr_t kOtbnSkHpk =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_sk_hpk);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024SkHpkWords, kOtbnSkHpk,
                              secret_key->keyblob + kMlkem1024SkSWords +
                                  kMlkem1024PkTWords + kMlkem1024PkRhoWords));

  const otbn_addr_t kOtbnSkZ =
      OTBN_ADDR_T_INIT(mlkem1024_keygen, mlkem1024_keygen_sk_z);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024SkZWords, kOtbnSkZ,
                              secret_key->keyblob + kMlkem1024SkSWords +
                                  kMlkem1024PkTWords + kMlkem1024PkRhoWords +
                                  kMlkem1024SkHpkWords));

  secret_key->checksum = otcrypto_integrity_blinded_checksum(secret_key);

  return OTCRYPTO_OK;
}

status_t mlkem1024_encaps_start(const otcrypto_unblinded_key_t *public_key,
                                const otcrypto_const_word32_buf_t *m) {
  // Securely wipe DMEM to initialize hardware SRAM ECC parity.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  // Load the ML-KEM-1024 encaps app.
  const otbn_app_t kOtbnAppMlkem1024Encaps = OTBN_APP_T_INIT(mlkem1024_encaps);
  HARDENED_TRY(otbn_load_app(kOtbnAppMlkem1024Encaps));

  // Write public key components.
  const otbn_addr_t kOtbnPkT =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_pk_t);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024PkTWords, public_key->key, kOtbnPkT));

  const otbn_addr_t kOtbnPkRho =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_pk_rho);
  HARDENED_TRY(otbn_dmem_write(
      kMlkem1024PkRhoWords, public_key->key + kMlkem1024PkTWords, kOtbnPkRho));

  // Write message m.
  const otbn_addr_t kOtbnM =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_m);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024SeedWords, m->data, kOtbnM));

  return otbn_execute();
}

status_t mlkem1024_encaps_finalize(otcrypto_word32_buf_t *ciphertext,
                                   otcrypto_blinded_key_t *shared_secret) {
  // Stall until OTBN finishes.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read ciphertext (ct_u: 1408 bytes, ct_v: 160 bytes).
  const otbn_addr_t kOtbnCtU =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_ct_u);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024CtUWords, kOtbnCtU, ciphertext->data));

  const otbn_addr_t kOtbnCtV =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_ct_v);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024CtVWords, kOtbnCtV,
                              ciphertext->data + kMlkem1024CtUWords));

  // Read shared secret (32 bytes).
  const otbn_addr_t kOtbnSs =
      OTBN_ADDR_T_INIT(mlkem1024_encaps, mlkem1024_encaps_ss);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024SharedSecretWords, kOtbnSs,
                              shared_secret->keyblob));

  shared_secret->checksum = otcrypto_integrity_blinded_checksum(shared_secret);

  return OTCRYPTO_OK;
}

status_t mlkem1024_decaps_start(const otcrypto_blinded_key_t *secret_key,
                                const otcrypto_const_word32_buf_t *ciphertext) {
  // Securely wipe DMEM to initialize hardware SRAM ECC parity.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  // Load the ML-KEM-1024 decaps app.
  const otbn_app_t kOtbnAppMlkem1024Decaps = OTBN_APP_T_INIT(mlkem1024_decaps);
  HARDENED_TRY(otbn_load_app(kOtbnAppMlkem1024Decaps));

  const otbn_addr_t kOtbnCtU =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_ct_u);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024CtUWords, ciphertext->data, kOtbnCtU));

  const otbn_addr_t kOtbnCtV =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_ct_v);
  HARDENED_TRY(otbn_dmem_write(
      kMlkem1024CtVWords, ciphertext->data + kMlkem1024CtUWords, kOtbnCtV));

  const otbn_addr_t kOtbnSkS =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_sk_s);
  HARDENED_TRY(
      otbn_dmem_write(kMlkem1024SkSWords, secret_key->keyblob, kOtbnSkS));

  const otbn_addr_t kOtbnSkPkT =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_sk_pk_t);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024PkTWords,
                               secret_key->keyblob + kMlkem1024SkSWords,
                               kOtbnSkPkT));

  const otbn_addr_t kOtbnSkPkRho =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_sk_pk_rho);
  HARDENED_TRY(otbn_dmem_write(
      kMlkem1024PkRhoWords,
      secret_key->keyblob + kMlkem1024SkSWords + kMlkem1024PkTWords,
      kOtbnSkPkRho));

  const otbn_addr_t kOtbnSkHpk =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_sk_hpk);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024SkHpkWords,
                               secret_key->keyblob + kMlkem1024SkSWords +
                                   kMlkem1024PkTWords + kMlkem1024PkRhoWords,
                               kOtbnSkHpk));

  const otbn_addr_t kOtbnSkZ =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_sk_z);
  HARDENED_TRY(otbn_dmem_write(kMlkem1024SkZWords,
                               secret_key->keyblob + kMlkem1024SkSWords +
                                   kMlkem1024PkTWords + kMlkem1024PkRhoWords +
                                   kMlkem1024SkHpkWords,
                               kOtbnSkZ));

  return otbn_execute();
}

status_t mlkem1024_decaps_finalize(otcrypto_blinded_key_t *shared_secret) {
  HARDENED_TRY(otbn_busy_wait_for_done());

  const otbn_addr_t kOtbnSs =
      OTBN_ADDR_T_INIT(mlkem1024_decaps, mlkem1024_decaps_ss);
  HARDENED_TRY(otbn_dmem_read(kMlkem1024SharedSecretWords, kOtbnSs,
                              shared_secret->keyblob));

  shared_secret->checksum = otcrypto_integrity_blinded_checksum(shared_secret);
  return OTCRYPTO_OK;
}
