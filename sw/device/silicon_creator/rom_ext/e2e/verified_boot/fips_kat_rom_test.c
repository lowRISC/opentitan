// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "hw/top/dt/aon_timer.h"
#include "hw/top/dt/csrng.h"
#include "hw/top/dt/entropy_src.h"
#include "hw/top/dt/rom_ctrl.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/aes_kwp/aes_kwp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"
#include "sw/device/lib/crypto/impl/mlkem/mlkem.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/kdf_ctr.h"
#include "sw/device/lib/crypto/include/kmac.h"
#include "sw/device/lib/crypto/include/kmac_kdf.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/crypto/include/mlkem.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_src_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/epmp_defs.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include "hw/top/csrng_regs.h"
#include "hw/top/entropy_src_regs.h"

// Keep OTTF alert monitoring enabled to ensure no recoverable or fatal alerts
// (e.g., from rom_ctrl ECC digest exposure or entropy misconfiguration) fire.
OTTF_DEFINE_TEST_CONFIG();

// Non-zero mask words used when constructing blinded keys for KATs.
static const uint32_t kTestMask[16] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5,
};

// -----------------------------------------------------------------------------
// Option B ePMP Negative Access-Fault Probing
// -----------------------------------------------------------------------------

static volatile bool expect_epmp_fault = false;
static volatile bool fault_observed = false;
static volatile uint32_t last_fault_mcause = 0;

void ottf_load_store_fault_handler(uint32_t *exc_info) {
  if (!expect_epmp_fault) {
    uint32_t mcause = ibex_mcause_read();
    ottf_generic_fault_print(exc_info, "Unexpected Load/Store Access Fault",
                             mcause);
    abort();
  }
  last_fault_mcause = ibex_mcause_read();
  fault_observed = true;
}

void ottf_instr_access_fault_handler(uint32_t *exc_info) {
  if (!expect_epmp_fault) {
    uint32_t mcause = ibex_mcause_read();
    ottf_generic_fault_print(exc_info, "Unexpected Instruction Access Fault",
                             mcause);
    abort();
  }
  last_fault_mcause = ibex_mcause_read();
  fault_observed = true;
  // Return to caller (`ra` is saved at exc_info[1]).
  exc_info[0] = exc_info[1];
}

static void assert_load_faults(uintptr_t addr) {
  fault_observed = false;
  last_fault_mcause = 0;
  expect_epmp_fault = true;
  volatile uint32_t val = *(const volatile uint32_t *)addr;
  (void)val;
  expect_epmp_fault = false;
  CHECK(fault_observed, "Expected load fault at 0x%08x", (uint32_t)addr);
  CHECK(last_fault_mcause == kIbexExcLoadAccessFault,
        "Expected LoadAccessFault at 0x%08x, got mcause=0x%08x", (uint32_t)addr,
        last_fault_mcause);
}

static void assert_store_faults(uintptr_t addr) {
  fault_observed = false;
  last_fault_mcause = 0;
  expect_epmp_fault = true;
  *(volatile uint32_t *)addr = 0u;
  expect_epmp_fault = false;
  CHECK(fault_observed, "Expected store fault at 0x%08x", (uint32_t)addr);
  CHECK(last_fault_mcause == kIbexExcStoreAccessFault,
        "Expected StoreAccessFault at 0x%08x, got mcause=0x%08x",
        (uint32_t)addr, last_fault_mcause);
}

static void assert_exec_faults(uintptr_t addr) {
  fault_observed = false;
  last_fault_mcause = 0;
  expect_epmp_fault = true;
  void (*fn)(void) = (void (*)(void))addr;
  fn();
  expect_epmp_fault = false;
  CHECK(fault_observed, "Expected exec fault at 0x%08x", (uint32_t)addr);
  CHECK(last_fault_mcause == kIbexExcInstrAccessFault,
        "Expected InstrAccessFault at 0x%08x, got mcause=0x%08x",
        (uint32_t)addr, last_fault_mcause);
}

static void map_rom_kat_slot0(uintptr_t base, size_t size) {
  uint32_t mseccfg = 0;
  CSR_READ(CSR_REG_MSECCFG, &mseccfg);
  CHECK((mseccfg & EPMP_MSECCFG_RLB) != 0, "mseccfg.RLB must be set");

  uint32_t pmpcfg0 = 0;
  CSR_READ(CSR_REG_PMPCFG0, &pmpcfg0);
  CHECK((pmpcfg0 & 0xFFu) == 0u, "ePMP slot 0 is already in use");

  const uint32_t pmpaddr = (uint32_t)((base >> 2) | ((size - 1u) >> 3));
  const uint32_t cfg = (uint32_t)(EPMP_CFG_LR | EPMP_CFG_A_NAPOT);
  CSR_WRITE(CSR_REG_PMPADDR0, pmpaddr);
  CSR_SET_BITS(CSR_REG_PMPCFG0, cfg);
}

static void unmap_rom_kat_slot0(void) {
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0xFFu);
  CSR_WRITE(CSR_REG_PMPADDR0, 0u);
}

// -----------------------------------------------------------------------------
// Lookup Helper
// -----------------------------------------------------------------------------

static const void *resolve_entry(const fips_kat_descriptor_table_t *table,
                                 fips_kat_alg_id_t alg_id,
                                 const fips_kat_entry_t **out_entry) {
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatRegionSize, alg_id);
  CHECK(entry != NULL, "Missing KAT entry for alg_id=%u", (uint32_t)alg_id);
  const void *data = get_fips_data(table, kFipsKatRegionSize, entry);
  CHECK(data != NULL, "Invalid KAT payload bounds for alg_id=%u",
        (uint32_t)alg_id);
  if (out_entry != NULL) {
    *out_entry = entry;
  }
  return data;
}

// -----------------------------------------------------------------------------
// Hash & MAC KATs (SHA2-256/384/512, HMAC-SHA2-256/512, SHAKE-256, KMAC-256)
// -----------------------------------------------------------------------------

static status_t test_sha256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)resolve_entry(
      table, kFipsKatAlgSha2_256, &entry);
  CHECK(entry->size == fips_kat_hmac_expected_size(kat));
  CHECK(kat->key_len == 0 && kat->digest_len == 32);

  const uint8_t *msg = fips_kat_hmac_msg(kat);
  const uint8_t *exp = fips_kat_hmac_digest(kat);

  // Verify via cryptolib FIPS API.
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, kat->msg_len);
  uint32_t digest_words[8] = {0};
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = ARRAYSIZE(digest_words),
      .data = digest_words,
  };
  CHECK_STATUS_OK(otcrypto_sha2_256(&msg_buf, &digest));
  CHECK_ARRAYS_EQ((const uint8_t *)digest_words, exp, 32);

  // Cross-check ROM/ROM_EXT silicon_creator driver compatibility.
  hmac_digest_t sc_digest;
  hmac_sha256(msg, kat->msg_len, &sc_digest);
  uint8_t sc_be[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t w = sc_digest.digest[7 - i];
    sc_be[4 * i] = (uint8_t)(w >> 24);
    sc_be[4 * i + 1] = (uint8_t)(w >> 16);
    sc_be[4 * i + 2] = (uint8_t)(w >> 8);
    sc_be[4 * i + 3] = (uint8_t)(w);
  }
  CHECK_ARRAYS_EQ(sc_be, exp, 32);
  return OK_STATUS();
}

static status_t test_sha512_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)resolve_entry(
      table, kFipsKatAlgSha2_512, &entry);
  CHECK(entry->size == fips_kat_hmac_expected_size(kat));
  CHECK(kat->key_len == 0 && kat->digest_len == 64);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_hmac_msg(kat), kat->msg_len);
  uint32_t digest_words[16] = {0};
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha512,
      .len = ARRAYSIZE(digest_words),
      .data = digest_words,
  };
  CHECK_STATUS_OK(otcrypto_sha2_512(&msg_buf, &digest));
  CHECK_ARRAYS_EQ((const uint8_t *)digest_words, fips_kat_hmac_digest(kat), 64);
  return OK_STATUS();
}

static status_t test_hmac_sha256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)resolve_entry(
      table, kFipsKatAlgHmacSha2_256, &entry);
  CHECK(entry->size == fips_kat_hmac_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->digest_len == 32);

  const uint8_t *key_bytes = fips_kat_hmac_key(kat);
  const uint8_t *msg = fips_kat_hmac_msg(kat);
  const uint8_t *exp = fips_kat_hmac_digest(kat);

  // Verify via cryptolib FIPS API.
  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask((const uint32_t *)key_bytes,
                                            kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, msg, kat->msg_len);
  uint32_t tag_words[8] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_words, ARRAYSIZE(tag_words));
  CHECK_STATUS_OK(otcrypto_hmac(&key, &msg_buf, &tag_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)tag_words, exp, 32);

  // Cross-check ROM/ROM_EXT silicon_creator HMAC driver compatibility (32B
  // key). Note: `sc_hmac_hmac_sha256` configures `KEY_SWAP = false`, so key
  // words must be packed big-endian.
  hmac_key_t sc_key;
  for (size_t i = 0; i < 8; ++i) {
    sc_key.key[i] = ((uint32_t)key_bytes[4 * i] << 24) |
                    ((uint32_t)key_bytes[4 * i + 1] << 16) |
                    ((uint32_t)key_bytes[4 * i + 2] << 8) |
                    (uint32_t)key_bytes[4 * i + 3];
  }
  hmac_digest_t sc_digest;
  sc_hmac_hmac_sha256(msg, kat->msg_len, sc_key, /*big_endian_digest=*/true,
                      &sc_digest);
  CHECK_ARRAYS_EQ((const uint8_t *)sc_digest.digest, exp, 32);
  return OK_STATUS();
}

static status_t test_hmac_sha512_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)resolve_entry(
      table, kFipsKatAlgHmacSha2_512, &entry);
  CHECK(entry->size == fips_kat_hmac_expected_size(kat));
  CHECK(kat->key_len == 64 && kat->digest_len == 64);

  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask(
      (const uint32_t *)fips_kat_hmac_key(kat), kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_hmac_msg(kat), kat->msg_len);
  uint32_t tag_words[16] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_words, ARRAYSIZE(tag_words));
  CHECK_STATUS_OK(otcrypto_hmac(&key, &msg_buf, &tag_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)tag_words, fips_kat_hmac_digest(kat), 64);
  return OK_STATUS();
}

static status_t test_shake256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)resolve_entry(
      table, kFipsKatAlgShake256, &entry);
  CHECK(entry->size == fips_kat_hmac_expected_size(kat));
  CHECK(kat->key_len == 0 && kat->digest_len == 32);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_hmac_msg(kat), kat->msg_len);
  uint32_t digest_words[8] = {0};
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashXofModeShake256,
      .len = ARRAYSIZE(digest_words),
      .data = digest_words,
  };
  CHECK_STATUS_OK(otcrypto_shake256(&msg_buf, &digest));
  CHECK_ARRAYS_EQ((const uint8_t *)digest_words, fips_kat_hmac_digest(kat), 32);
  return OK_STATUS();
}

static status_t test_kmac256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const kdf_kat_data_t *kat =
      (const kdf_kat_data_t *)resolve_entry(table, kFipsKatAlgKmac256, &entry);
  CHECK(entry->size == fips_kat_kdf_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->out_len == 64);

  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeKmac256,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask(
      (const uint32_t *)fips_kat_kdf_key(kat), kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  otcrypto_const_byte_buf_t custom_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_label(kat), kat->label_len);
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_context(kat), kat->context_len);
  uint32_t tag_words[16] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_words, ARRAYSIZE(tag_words));
  CHECK_STATUS_OK(
      otcrypto_kmac(&key, &msg_buf, &custom_buf, kat->out_len, &tag_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)tag_words, fips_kat_kdf_out(kat), 64);
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// AES KATs (ECB-256, CBC-256 2-block, KWP-256 9B padded, GCM-256 CAVP)
// -----------------------------------------------------------------------------

static status_t test_aes_ecb256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const aes_kat_data_t *kat = (const aes_kat_data_t *)resolve_entry(
      table, kFipsKatAlgAesEcb256Decrypt, &entry);
  CHECK(entry->size == fips_kat_aes_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->pt_len == 16 && kat->ct_len == 16);

  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesEcb,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask(
      (const uint32_t *)fips_kat_aes_key(kat), kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  uint32_t dummy_iv_words[4] = {0};
  otcrypto_word32_buf_t iv = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, dummy_iv_words, ARRAYSIZE(dummy_iv_words));

  // Decrypt KAT.
  uint32_t pt_out[4] = {0};
  otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_ct(kat), kat->ct_len);
  otcrypto_byte_buf_t pt_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)pt_out, kat->pt_len);
  CHECK_STATUS_OK(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                               kOtcryptoAesOperationDecrypt, &ct_in,
                               kOtcryptoAesPaddingNull, &pt_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)pt_out, fips_kat_aes_pt(kat), 16);

  // Encrypt KAT.
  uint32_t ct_out[4] = {0};
  otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_pt(kat), kat->pt_len);
  otcrypto_byte_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)ct_out, kat->ct_len);
  CHECK_STATUS_OK(otcrypto_aes(&key, &iv, kOtcryptoAesModeEcb,
                               kOtcryptoAesOperationEncrypt, &pt_in,
                               kOtcryptoAesPaddingNull, &ct_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)ct_out, fips_kat_aes_ct(kat), 16);
  return OK_STATUS();
}

static status_t test_aes_cbc256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const aes_kat_data_t *kat = (const aes_kat_data_t *)resolve_entry(
      table, kFipsKatAlgAesCbc256Decrypt, &entry);
  CHECK(entry->size == fips_kat_aes_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->iv_len == 16 && kat->pt_len == 32 &&
        kat->ct_len == 32);

  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCbc,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask(
      (const uint32_t *)fips_kat_aes_key(kat), kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  // Decrypt 2-block CBC KAT.
  uint32_t iv_words[4];
  memcpy(iv_words, fips_kat_aes_iv(kat), 16);
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_words, ARRAYSIZE(iv_words));
  uint32_t pt_out[8] = {0};
  otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_ct(kat), kat->ct_len);
  otcrypto_byte_buf_t pt_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)pt_out, kat->pt_len);
  CHECK_STATUS_OK(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                               kOtcryptoAesOperationDecrypt, &ct_in,
                               kOtcryptoAesPaddingNull, &pt_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)pt_out, fips_kat_aes_pt(kat), 32);

  // Encrypt 2-block CBC KAT.
  memcpy(iv_words, fips_kat_aes_iv(kat), 16);
  uint32_t ct_out[8] = {0};
  otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_pt(kat), kat->pt_len);
  otcrypto_byte_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)ct_out, kat->ct_len);
  CHECK_STATUS_OK(otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc,
                               kOtcryptoAesOperationEncrypt, &pt_in,
                               kOtcryptoAesPaddingNull, &ct_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)ct_out, fips_kat_aes_ct(kat), 32);
  return OK_STATUS();
}

static status_t test_aes_kwp256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const aes_kat_data_t *kat = (const aes_kat_data_t *)resolve_entry(
      table, kFipsKatAlgAesKwp256Wrap, &entry);
  CHECK(entry->size == fips_kat_aes_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->pt_len == 9 && kat->ct_len == 24);

  uint32_t kek_share0[8];
  const uint32_t *raw_kek = (const uint32_t *)fips_kat_aes_key(kat);
  for (size_t i = 0; i < 8; ++i) {
    kek_share0[i] = raw_kek[i] ^ kTestMask[i];
  }
  aes_key_t aes_kek = {
      .mode = kAesCipherModeEcb,
      .sideload = kHardenedBoolFalse,
      .key_len = 8,
      .key_shares = {kek_share0, kTestMask},
  };
  aes_kek.checksum = aes_key_integrity_checksum(&aes_kek);

  // Wrap 9-byte plaintext (exercises RFC 5649 non-multiple-of-8 padding).
  uint32_t act_ct[6] = {0};
  CHECK_STATUS_OK(aes_kwp_wrap(aes_kek, (const uint32_t *)fips_kat_aes_pt(kat),
                               kat->pt_len, act_ct));
  CHECK_ARRAYS_EQ((const uint8_t *)act_ct, fips_kat_aes_ct(kat), 24);

  // Unwrap and verify recovered length and bytes.
  uint32_t act_pt[3] = {0};
  hardened_bool_t success = kHardenedBoolFalse;
  size_t act_pt_len = 0;
  CHECK_STATUS_OK(aes_kwp_unwrap(aes_kek,
                                 (const uint32_t *)fips_kat_aes_ct(kat),
                                 kat->ct_len, &success, act_pt, &act_pt_len));
  CHECK(success == kHardenedBoolTrue);
  CHECK(act_pt_len == kat->pt_len);
  CHECK_ARRAYS_EQ((const uint8_t *)act_pt, fips_kat_aes_pt(kat), kat->pt_len);
  return OK_STATUS();
}

static status_t test_aes_gcm256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const aes_kat_data_t *kat = (const aes_kat_data_t *)resolve_entry(
      table, kFipsKatAlgAesGcm256Encrypt, &entry);
  CHECK(entry->size == fips_kat_aes_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->iv_len == 12 && kat->aad_len == 16 &&
        kat->pt_len == 51 && kat->ct_len == 51 && kat->tag_len == 16);

  const otcrypto_key_config_t kConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kConfig)];
  CHECK_STATUS_OK(keyblob_from_key_and_mask(
      (const uint32_t *)fips_kat_aes_key(kat), kTestMask, kConfig, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  otcrypto_const_word32_buf_t iv_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, (const uint32_t *)fips_kat_aes_iv(kat), 3);
  otcrypto_const_byte_buf_t aad_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_aad(kat), kat->aad_len);
  otcrypto_const_byte_buf_t pt_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_pt(kat), kat->pt_len);

  uint8_t act_ct[51] = {0};
  otcrypto_byte_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, act_ct, sizeof(act_ct));
  uint32_t act_tag[4] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, ARRAYSIZE(act_tag));
  CHECK_STATUS_OK(otcrypto_aes_gcm_encrypt(&key, &pt_in, &iv_buf, &aad_buf,
                                           kOtcryptoAesGcmTagLen128, &ct_buf,
                                           &tag_buf));
  CHECK_ARRAYS_EQ(act_ct, fips_kat_aes_ct(kat), 51);
  CHECK_ARRAYS_EQ((const uint8_t *)act_tag, fips_kat_aes_tag(kat), 16);

  uint8_t act_pt[51] = {0};
  otcrypto_byte_buf_t pt_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, act_pt, sizeof(act_pt));
  otcrypto_const_byte_buf_t ct_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_aes_ct(kat), kat->ct_len);
  otcrypto_const_word32_buf_t exp_tag_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, (const uint32_t *)fips_kat_aes_tag(kat), 4);
  hardened_bool_t success = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_aes_gcm_decrypt(&key, &ct_in, &iv_buf, &aad_buf,
                                           kOtcryptoAesGcmTagLen128,
                                           &exp_tag_buf, &pt_buf, &success));
  CHECK(success == kHardenedBoolTrue);
  CHECK_ARRAYS_EQ(act_pt, fips_kat_aes_pt(kat), 51);
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// KDF KATs (KDF-CTR-HMAC-SHA256, KDF-KMAC-256, HKDF-SHA2-384)
// -----------------------------------------------------------------------------

static status_t test_kdf_hmac_sha256_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const kdf_kat_data_t *kat = (const kdf_kat_data_t *)resolve_entry(
      table, kFipsKatAlgKdfHmacSha2_256, &entry);
  CHECK(entry->size == fips_kat_kdf_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->out_len == 48);

  const otcrypto_key_config_t kKdkConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t kdk_blob[keyblob_num_words(kKdkConfig)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask((const uint32_t *)fips_kat_kdf_key(kat),
                                kTestMask, kKdkConfig, kdk_blob));
  otcrypto_blinded_key_t kdk = {
      .config = kKdkConfig,
      .keyblob_length = sizeof(kdk_blob),
      .keyblob = kdk_blob,
  };
  kdk.checksum = otcrypto_integrity_blinded_checksum(&kdk);

  const otcrypto_key_config_t kOkmConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_length = kat->out_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t okm_blob[keyblob_num_words(kOkmConfig)];
  memset(okm_blob, 0, sizeof(okm_blob));
  otcrypto_blinded_key_t okm = {
      .config = kOkmConfig,
      .keyblob_length = sizeof(okm_blob),
      .keyblob = okm_blob,
  };

  otcrypto_const_byte_buf_t label_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_label(kat), kat->label_len);
  otcrypto_const_byte_buf_t context_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_context(kat), kat->context_len);
  CHECK_STATUS_OK(otcrypto_kdf_ctr_hmac(&kdk, &label_buf, &context_buf, &okm));
  CHECK(otcrypto_integrity_blinded_key_check(&okm) == kHardenedBoolTrue);

  uint32_t act_okm[12] = {0};
  CHECK_STATUS_OK(keyblob_key_unmask(&okm, ARRAYSIZE(act_okm), act_okm));
  CHECK_ARRAYS_EQ((const uint8_t *)act_okm, fips_kat_kdf_out(kat), 48);
  return OK_STATUS();
}

static status_t test_kdf_kmac256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const kdf_kat_data_t *kat = (const kdf_kat_data_t *)resolve_entry(
      table, kFipsKatAlgKdfKmac256, &entry);
  CHECK(entry->size == fips_kat_kdf_expected_size(kat));
  CHECK(kat->key_len == 32 && kat->out_len == 48);

  const otcrypto_key_config_t kKdkConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeKdfKmac256,
      .key_length = kat->key_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t kdk_blob[keyblob_num_words(kKdkConfig)];
  CHECK_STATUS_OK(
      keyblob_from_key_and_mask((const uint32_t *)fips_kat_kdf_key(kat),
                                kTestMask, kKdkConfig, kdk_blob));
  otcrypto_blinded_key_t kdk = {
      .config = kKdkConfig,
      .keyblob_length = sizeof(kdk_blob),
      .keyblob = kdk_blob,
  };
  kdk.checksum = otcrypto_integrity_blinded_checksum(&kdk);

  const otcrypto_key_config_t kOkmConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_length = kat->out_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t okm_blob[keyblob_num_words(kOkmConfig)];
  memset(okm_blob, 0, sizeof(okm_blob));
  otcrypto_blinded_key_t okm = {
      .config = kOkmConfig,
      .keyblob_length = sizeof(okm_blob),
      .keyblob = okm_blob,
  };

  otcrypto_const_byte_buf_t label_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_label(kat), kat->label_len);
  otcrypto_const_byte_buf_t context_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_kdf_context(kat), kat->context_len);
  CHECK_STATUS_OK(otcrypto_kmac_kdf(&kdk, &label_buf, &context_buf, &okm));
  CHECK(otcrypto_integrity_blinded_key_check(&okm) == kHardenedBoolTrue);

  uint32_t act_okm[12] = {0};
  CHECK_STATUS_OK(keyblob_key_unmask(&okm, ARRAYSIZE(act_okm), act_okm));
  CHECK_ARRAYS_EQ((const uint8_t *)act_okm, fips_kat_kdf_out(kat), 48);
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// Asymmetric KATs (RSA-2048/4096, ECDSA P-256/P-384, Ed25519, ECDH, X25519)
// -----------------------------------------------------------------------------

static status_t test_rsa2048_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgRsa2048Verify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 256 && kat->pub_key_len2 == 4 &&
        kat->sig_len1 == 256);

  otcrypto_const_word32_buf_t mod_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t,
      (const uint32_t *)fips_kat_asym_verify_pub_key1(kat), 64);
  uint32_t pk_data[kOtcryptoRsa2048PublicKeyBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pk_data,
  };
  CHECK_STATUS_OK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048,
                                                    &mod_buf, &public_key));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_verify_msg(kat), kat->msg_len);
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t,
                        (const uint32_t *)fips_kat_asym_verify_sig1(kat), 64);
  hardened_bool_t result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_rsa_hash_verify(&public_key, kOtcryptoHashModeSha256,
                                           &msg_buf, kOtcryptoRsaPaddingPkcs,
                                           &sig_buf, &result));
  CHECK(result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t test_rsa4096_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_sign_kat_data_t *kat =
      (const asymmetric_sign_kat_data_t *)resolve_entry(
          table, kFipsKatAlgRsa4096Sign, &entry);
  CHECK(entry->size == fips_kat_asym_sign_expected_size(kat));
  CHECK(kat->priv_key_len == 1024 && kat->sig_len1 == 512);

  const uint32_t *modulus = (const uint32_t *)fips_kat_asym_sign_priv_key(kat);
  const uint32_t *d_share0 = modulus + 128;
  static uint32_t zero_share[128] = {0};

  otcrypto_const_word32_buf_t mod_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, modulus, 128);
  otcrypto_const_word32_buf_t d0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d_share0, 128);
  otcrypto_const_word32_buf_t d1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, zero_share, 128);

  const otcrypto_key_config_t kPrivConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  static uint32_t
      keyblob[kOtcryptoRsa4096PrivateKeyblobBytes / sizeof(uint32_t)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivConfig,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes,
  };
  CHECK_STATUS_OK(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize4096, &mod_buf, &d0_buf, &d1_buf, &private_key));

  static uint32_t pub_data[kOtcryptoRsa4096PublicKeyBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
      .key = pub_data,
  };
  CHECK_STATUS_OK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096,
                                                    &mod_buf, &public_key));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_sign_msg(kat), kat->msg_len);
  static uint32_t act_sig[128];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_sig, ARRAYSIZE(act_sig));
  CHECK_STATUS_OK(otcrypto_rsa_hash_sign_verify(
      &private_key, &public_key, kOtcryptoHashModeSha512, &msg_buf,
      kOtcryptoRsaPaddingPkcs, &sig_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)act_sig, fips_kat_asym_sign_sig1(kat), 512);
  return OK_STATUS();
}

static status_t test_rsa4096_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgRsa4096Verify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 512 && kat->pub_key_len2 == 4 &&
        kat->sig_len1 == 512);

  otcrypto_const_word32_buf_t mod_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t,
      (const uint32_t *)fips_kat_asym_verify_pub_key1(kat), 128);
  static uint32_t pk_data[kOtcryptoRsa4096PublicKeyBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
      .key = pk_data,
  };
  CHECK_STATUS_OK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096,
                                                    &mod_buf, &public_key));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_verify_msg(kat), kat->msg_len);
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t,
                        (const uint32_t *)fips_kat_asym_verify_sig1(kat), 128);
  hardened_bool_t result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_rsa_hash_verify(&public_key, kOtcryptoHashModeSha512,
                                           &msg_buf, kOtcryptoRsaPaddingPkcs,
                                           &sig_buf, &result));
  CHECK(result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t test_ecdsa_p256_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_sign_kat_data_t *kat =
      (const asymmetric_sign_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEcdsaP256Sign, &entry);
  CHECK(entry->size == fips_kat_asym_sign_expected_size(kat));
  CHECK(kat->priv_key_len == 32 && kat->ephemeral_len == 32 &&
        kat->msg_len == 128 && kat->sig_len1 == 32 && kat->sig_len2 == 32);

  const otcrypto_key_config_t kP256Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob_sk[20] = {0};
  memcpy(keyblob_sk, fips_kat_asym_sign_priv_key(kat), 32);
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t keyblob_k[20] = {0};
  memcpy(keyblob_k, fips_kat_asym_sign_ephemeral(kat), 32);
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_k),
      .keyblob = keyblob_k,
  };
  secret_scalar.checksum = otcrypto_integrity_blinded_checksum(&secret_scalar);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_sign_msg(kat), kat->msg_len);
  uint32_t digest_words[8] = {0};
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = ARRAYSIZE(digest_words),
      .data = digest_words,
  };
  CHECK_STATUS_OK(otcrypto_sha2_256(&msg_buf, &digest));

  uint32_t sig[16] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_sign_config_k(
      &private_key, &secret_scalar, digest, &sig_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)sig, fips_kat_asym_sign_sig1(kat), 32);
  CHECK_ARRAYS_EQ((const uint8_t *)(sig + 8), fips_kat_asym_sign_sig2(kat), 32);
  return OK_STATUS();
}

static status_t test_ecdsa_p256_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEcdsaP256Verify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 32 && kat->pub_key_len2 == 32 &&
        kat->msg_len == 128 && kat->sig_len1 == 32 && kat->sig_len2 == 32);

  uint32_t pk_words[16];
  memcpy(pk_words, fips_kat_asym_verify_pub_key1(kat), 32);
  memcpy(pk_words + 8, fips_kat_asym_verify_pub_key2(kat), 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_verify_msg(kat), kat->msg_len);
  uint32_t sig_words[16];
  memcpy(sig_words, fips_kat_asym_verify_sig1(kat), 32);
  memcpy(sig_words + 8, fips_kat_asym_verify_sig2(kat), 32);
  otcrypto_const_word32_buf_t sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));

  hardened_bool_t result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_hash_verify(
      &public_key, kOtcryptoHashModeSha256, &msg_buf, &sig_buf, &result));
  CHECK(result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t test_ecdsa_p384_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_sign_kat_data_t *kat =
      (const asymmetric_sign_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEcdsaP384Sign, &entry);
  CHECK(entry->size == fips_kat_asym_sign_expected_size(kat));
  CHECK(kat->priv_key_len == 48 && kat->ephemeral_len == 48 &&
        kat->msg_len == 128 && kat->sig_len1 == 48 && kat->sig_len2 == 48);

  const otcrypto_key_config_t kP384Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 48,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob_sk[28] = {0};
  memcpy(keyblob_sk, fips_kat_asym_sign_priv_key(kat), 48);
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t keyblob_k[28] = {0};
  memcpy(keyblob_k, fips_kat_asym_sign_ephemeral(kat), 48);
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_k),
      .keyblob = keyblob_k,
  };
  secret_scalar.checksum = otcrypto_integrity_blinded_checksum(&secret_scalar);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_sign_msg(kat), kat->msg_len);
  uint32_t digest_words[12] = {0};
  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = ARRAYSIZE(digest_words),
      .data = digest_words,
  };
  CHECK_STATUS_OK(otcrypto_sha2_384(&msg_buf, &digest));

  uint32_t sig[24] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_config_k(
      &private_key, &secret_scalar, digest, &sig_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)sig, fips_kat_asym_sign_sig1(kat), 48);
  CHECK_ARRAYS_EQ((const uint8_t *)(sig + 12), fips_kat_asym_sign_sig2(kat),
                  48);
  return OK_STATUS();
}

static status_t test_ecdsa_p384_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEcdsaP384Verify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 48 && kat->pub_key_len2 == 48 &&
        kat->msg_len == 128 && kat->sig_len1 == 48 && kat->sig_len2 == 48);

  uint32_t pk_words[24];
  memcpy(pk_words, fips_kat_asym_verify_pub_key1(kat), 48);
  memcpy(pk_words + 12, fips_kat_asym_verify_pub_key2(kat), 48);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_verify_msg(kat), kat->msg_len);
  uint32_t sig_words[24];
  memcpy(sig_words, fips_kat_asym_verify_sig1(kat), 48);
  memcpy(sig_words + 12, fips_kat_asym_verify_sig2(kat), 48);
  otcrypto_const_word32_buf_t sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));

  hardened_bool_t result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_hash_verify(
      &public_key, kOtcryptoHashModeSha384, &msg_buf, &sig_buf, &result));
  CHECK(result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t test_ed25519_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_sign_kat_data_t *kat =
      (const asymmetric_sign_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEd25519Sign, &entry);
  CHECK(entry->size == fips_kat_asym_sign_expected_size(kat));
  CHECK(kat->priv_key_len == 32 && kat->msg_len == 1 && kat->sig_len1 == 32 &&
        kat->sig_len2 == 32);

  const otcrypto_key_config_t kEd25519Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kEd25519Config)];
  memset(keyblob, 0, sizeof(keyblob));
  memcpy(keyblob, fips_kat_asym_sign_priv_key(kat), 32);
  otcrypto_blinded_key_t private_key = {
      .config = kEd25519Config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_sign_msg(kat), kat->msg_len);
  uint32_t sig[16] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  CHECK_STATUS_OK(otcrypto_ed25519_sign(&private_key, &msg_buf,
                                        kOtcryptoEddsaSignModeEddsa, &sig_buf));
  CHECK_ARRAYS_EQ((const uint8_t *)sig, fips_kat_asym_sign_sig1(kat), 32);
  CHECK_ARRAYS_EQ((const uint8_t *)(sig + 8), fips_kat_asym_sign_sig2(kat), 32);
  return OK_STATUS();
}

static status_t test_ed25519_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgEd25519Verify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 32 && kat->msg_len == 1 && kat->sig_len1 == 32 &&
        kat->sig_len2 == 32);

  uint32_t pk_words[8];
  memcpy(pk_words, fips_kat_asym_verify_pub_key1(kat), 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, fips_kat_asym_verify_msg(kat), kat->msg_len);
  uint32_t sig_words[16];
  memcpy(sig_words, fips_kat_asym_verify_sig1(kat), 32);
  memcpy(sig_words + 8, fips_kat_asym_verify_sig2(kat), 32);
  otcrypto_const_word32_buf_t sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));

  hardened_bool_t result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ed25519_verify(
      &public_key, &msg_buf, kOtcryptoEddsaSignModeEddsa, &sig_buf, &result));
  CHECK(result == kHardenedBoolTrue);
  return OK_STATUS();
}

static status_t test_ecdh_p256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const ecdh_kat_data_t *kat = (const ecdh_kat_data_t *)resolve_entry(
      table, kFipsKatAlgEcdhP256, &entry);
  CHECK(entry->size == fips_kat_ecdh_expected_size(kat));
  CHECK(kat->priv_key_len == 32 && kat->pub_key_len1 == 32 &&
        kat->pub_key_len2 == 32 && kat->shared_secret_len == 32);

  const otcrypto_key_config_t kP256Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob_sk[20] = {0};
  memcpy(keyblob_sk, fips_kat_ecdh_priv_key(kat), 32);
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_words[16];
  memcpy(pk_words, fips_kat_ecdh_pub_key1(kat), 32);
  memcpy(pk_words + 8, fips_kat_ecdh_pub_key2(kat), 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  const otcrypto_key_config_t kSsConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = 64,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t ss_blob[32] = {0};
  otcrypto_blinded_key_t shared_secret = {
      .config = kSsConfig,
      .keyblob_length = sizeof(ss_blob),
      .keyblob = ss_blob,
  };
  CHECK_STATUS_OK(
      otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret));

  uint32_t ss_words[16] = {0};
  CHECK_STATUS_OK(
      keyblob_key_unmask(&shared_secret, ARRAYSIZE(ss_words), ss_words));
  CHECK_ARRAYS_EQ((const uint8_t *)ss_words, fips_kat_ecdh_shared_secret(kat),
                  32);
  return OK_STATUS();
}

static status_t test_ecdh_p384_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const ecdh_kat_data_t *kat = (const ecdh_kat_data_t *)resolve_entry(
      table, kFipsKatAlgEcdhP384, &entry);
  CHECK(entry->size == fips_kat_ecdh_expected_size(kat));
  CHECK(kat->priv_key_len == 48 && kat->pub_key_len1 == 48 &&
        kat->pub_key_len2 == 48 && kat->shared_secret_len == 48);

  const otcrypto_key_config_t kP384Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = 48,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob_sk[28] = {0};
  memcpy(keyblob_sk, fips_kat_ecdh_priv_key(kat), 48);
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_words[24];
  memcpy(pk_words, fips_kat_ecdh_pub_key1(kat), 48);
  memcpy(pk_words + 12, fips_kat_ecdh_pub_key2(kat), 48);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  const otcrypto_key_config_t kSsConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = 96,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t ss_blob[48] = {0};
  otcrypto_blinded_key_t shared_secret = {
      .config = kSsConfig,
      .keyblob_length = sizeof(ss_blob),
      .keyblob = ss_blob,
  };
  CHECK_STATUS_OK(
      otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret));

  uint32_t ss_words[24] = {0};
  CHECK_STATUS_OK(
      keyblob_key_unmask(&shared_secret, ARRAYSIZE(ss_words), ss_words));
  CHECK_ARRAYS_EQ((const uint8_t *)ss_words, fips_kat_ecdh_shared_secret(kat),
                  48);
  return OK_STATUS();
}

static status_t test_x25519_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const ecdh_kat_data_t *kat =
      (const ecdh_kat_data_t *)resolve_entry(table, kFipsKatAlgX25519, &entry);
  CHECK(entry->size == fips_kat_ecdh_expected_size(kat));
  CHECK(kat->priv_key_len == 32 && kat->pub_key_len1 == 32 &&
        kat->shared_secret_len == 32);

  const otcrypto_key_config_t kX25519Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob_sk[keyblob_num_words(kX25519Config)];
  memset(keyblob_sk, 0, sizeof(keyblob_sk));
  memcpy(keyblob_sk, fips_kat_ecdh_priv_key(kat), 32);
  otcrypto_blinded_key_t private_key = {
      .config = kX25519Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_words[8];
  memcpy(pk_words, fips_kat_ecdh_pub_key1(kat), 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = sizeof(pk_words),
      .key = pk_words,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  uint32_t ss_blob[keyblob_num_words(kX25519Config)];
  memset(ss_blob, 0, sizeof(ss_blob));
  otcrypto_blinded_key_t shared_secret = {
      .config = kX25519Config,
      .keyblob_length = sizeof(ss_blob),
      .keyblob = ss_blob,
  };
  CHECK_STATUS_OK(otcrypto_x25519(&private_key, &public_key, &shared_secret));

  uint32_t *ss_share0;
  uint32_t *ss_share1;
  CHECK_STATUS_OK(keyblob_to_shares(&shared_secret, &ss_share0, &ss_share1));
  uint32_t ss[8];
  for (size_t i = 0; i < 8; ++i) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }
  CHECK_ARRAYS_EQ((const uint8_t *)ss, fips_kat_ecdh_shared_secret(kat), 32);
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// Post-Quantum KATs (ML-DSA-87, ML-KEM-1024, NIST Round 3 SPHINCS+)
// -----------------------------------------------------------------------------

static status_t test_sphincsplus_sha2_128s_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const asymmetric_verify_kat_data_t *kat =
      (const asymmetric_verify_kat_data_t *)resolve_entry(
          table, kFipsKatAlgSphincsPlusSha2_128sVerify, &entry);
  CHECK(entry->size == fips_kat_asym_verify_expected_size(kat));
  CHECK(kat->pub_key_len1 == 32 && kat->msg_len == 33 && kat->sig_len1 == 7856);

  const uint32_t *pk_words =
      (const uint32_t *)fips_kat_asym_verify_pub_key1(kat);
  const uint8_t *msg_bytes = fips_kat_asym_verify_msg(kat);
  const uint32_t *sig_words = (const uint32_t *)fips_kat_asym_verify_sig1(kat);

  uint32_t exp_root[kSpxVerifyRootNumWords];
  spx_public_key_root(pk_words, exp_root);

  uint32_t act_root[kSpxVerifyRootNumWords];
  rom_error_t err = spx_verify(sig_words, NULL, 0, NULL, 0, NULL, 0, msg_bytes,
                               kat->msg_len, pk_words, act_root);
  CHECK(err == kErrorOk, "spx_verify failed: 0x%08x", err);
  CHECK_ARRAYS_EQ(act_root, exp_root, kSpxVerifyRootNumWords);
  return OK_STATUS();
}

static status_t test_mldsa87_kat(const fips_kat_descriptor_table_t *table,
                                 const dif_aon_timer_t *aon_timer) {
  const fips_kat_entry_t *entry;
  const mldsa_kat_data_t *kat = (const mldsa_kat_data_t *)resolve_entry(
      table, kFipsKatAlgMldsa87, &entry);
  CHECK(kat->num_cases == 5 &&
        entry->size == fips_kat_mldsa_expected_size(kat));

  static uint32_t pk_data[kOtcryptoMldsa87PkWords];
  static uint32_t sk_data[kOtcryptoMldsa87SkWords];
  static uint32_t sig_data[kOtcryptoMldsa87SigWords];

  for (size_t i = 0; i < kat->num_cases; ++i) {
    CHECK_DIF_OK(dif_aon_timer_watchdog_pet(aon_timer));
    const fips_kat_mldsa87_case_t *c = &kat->cases[i];

    uint32_t xi_data[16] = {0};
    memcpy(xi_data, c->seed, 32);
    otcrypto_blinded_key_t xi = {
        .config =
            {
                .version = kOtcryptoLibVersion1,
                .key_mode = kOtcryptoKeyModePqcMldsa87,
                .key_length = 64,
                .hw_backed = kHardenedBoolFalse,
                .exportable = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = sizeof(xi_data),
        .keyblob = xi_data,
    };
    xi.checksum = otcrypto_integrity_blinded_checksum(&xi);

    otcrypto_unblinded_key_t pk = {
        .key_mode = kOtcryptoKeyModePqcMldsa87,
        .key_length = kOtcryptoMldsa87PkBytes,
        .key = pk_data,
    };
    otcrypto_blinded_key_t sk = {
        .config =
            {
                .version = kOtcryptoLibVersion1,
                .key_mode = kOtcryptoKeyModePqcMldsa87,
                .key_length = kOtcryptoMldsa87SkBytes,
                .hw_backed = kHardenedBoolFalse,
                .exportable = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = kOtcryptoMldsa87SkBytes,
        .keyblob = sk_data,
    };

    CHECK_STATUS_OK(mldsa87_det_keygen_internal_start(&xi));
    CHECK_STATUS_OK(mldsa87_keygen_internal_finalize(&pk, &sk));
    pk.checksum = otcrypto_integrity_unblinded_checksum(&pk);
    sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

    // mu = SHAKE256(tr || M', 64)
    otcrypto_sha3_context_t sha3_ctx;
    CHECK_STATUS_OK(otcrypto_shake256_init(&sha3_ctx));
    otcrypto_const_byte_buf_t tr_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                          (const unsigned char *)(sk.keyblob + 24), 64);
    CHECK_STATUS_OK(otcrypto_sha3_update(&sha3_ctx, &tr_buf));
    otcrypto_const_byte_buf_t mprime_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, c->mprime, sizeof(c->mprime));
    CHECK_STATUS_OK(otcrypto_sha3_update(&sha3_ctx, &mprime_buf));

    uint32_t mu_data[16] = {0};
    otcrypto_hash_digest_t mu = {
        .mode = kOtcryptoHashXofModeShake256,
        .len = ARRAYSIZE(mu_data),
        .data = mu_data,
    };
    CHECK_STATUS_OK(otcrypto_shake256_final(&sha3_ctx, &mu));

    CHECK_STATUS_OK(
        mldsa87_sign_internal_start(&sk, &mu, kOtcryptoMldsaSignModeDet));
    otcrypto_word32_buf_t sig_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, sig_data, kOtcryptoMldsa87SigWords);
    CHECK_STATUS_OK(
        mldsa87_sign_internal_finalize(&sig_buf, kMldsa87SingleSign));

    // Verify SHA2-256(sig[0..4627]) matches ROM expected hash.
    uint32_t act_sig_hash[8] = {0};
    otcrypto_hash_digest_t sig_hash = {
        .mode = kOtcryptoHashModeSha256,
        .len = ARRAYSIZE(act_sig_hash),
        .data = act_sig_hash,
    };
    otcrypto_const_byte_buf_t sig_bytes_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (const unsigned char *)sig_data, 4627);
    CHECK_STATUS_OK(otcrypto_sha2_256(&sig_bytes_buf, &sig_hash));
    CHECK_ARRAYS_EQ((const uint8_t *)act_sig_hash, c->expected_sig_hash, 32);

    // Verify generated signature on OTBN.
    otcrypto_const_word32_buf_t const_sig_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, sig_data, kOtcryptoMldsa87SigWords);
    CHECK_STATUS_OK(mldsa87_verify_internal_start(&pk, &const_sig_buf, &mu));
    hardened_bool_t result = kHardenedBoolFalse;
    CHECK_STATUS_OK(mldsa87_verify_internal_finalize(&const_sig_buf, &result));
    CHECK(result == kHardenedBoolTrue);
  }
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// DRBG (SP 800-90A Section 11.3) & Entropy Source SHA3 Conditioning KATs
// -----------------------------------------------------------------------------

static void check_csrng_sw_state(const drbg_kat_state_t *expected) {
  const uint32_t kBase = dt_csrng_primary_reg_block(kDtCsrng);
  uint32_t reg = bitfield_field32_write(
      0, CSRNG_INT_STATE_NUM_INT_STATE_NUM_FIELD, /*SwInstance=*/2u);
  abs_mmio_write32(kBase + CSRNG_INT_STATE_NUM_REG_OFFSET, reg);

  drbg_kat_state_t got = {0};
  got.reseed_counter = abs_mmio_read32(kBase + CSRNG_INT_STATE_VAL_REG_OFFSET);
  for (size_t i = 0; i < ARRAYSIZE(got.v); ++i) {
    got.v[i] = abs_mmio_read32(kBase + CSRNG_INT_STATE_VAL_REG_OFFSET);
  }
  for (size_t i = 0; i < ARRAYSIZE(got.key); ++i) {
    got.key[i] = abs_mmio_read32(kBase + CSRNG_INT_STATE_VAL_REG_OFFSET);
  }
  uint32_t flags = abs_mmio_read32(kBase + CSRNG_INT_STATE_VAL_REG_OFFSET);
  bool instantiated = bitfield_bit32_read(flags, 0u);
  bool fips = bitfield_bit32_read(flags, 1u);

  CHECK(instantiated && !fips, "Unexpected CSRNG flags: 0x%08x", flags);
  CHECK(got.reseed_counter == expected->reseed_counter);
  CHECK_ARRAYS_EQ(got.v, expected->v, ARRAYSIZE(got.v));
  CHECK_ARRAYS_EQ(got.key, expected->key, ARRAYSIZE(got.key));
}

static status_t test_drbg_aes256_kat(const fips_kat_descriptor_table_t *table) {
  const fips_kat_entry_t *entry;
  const drbg_kat_data_t *kat = (const drbg_kat_data_t *)resolve_entry(
      table, kFipsKatAlgDrbgAes256, &entry);
  CHECK(entry->size == sizeof(drbg_kat_data_t));
  CHECK(kat->seed_len == 48 && kat->expected_output_len == 64);

  CHECK_STATUS_OK(entropy_csrng_uninstantiate());

  entropy_seed_material_t seed = {.len = 12};
  memcpy(seed.data, kat->seed_instantiate, sizeof(seed.data));
  CHECK_STATUS_OK(entropy_csrng_instantiate(kHardenedBoolTrue, &seed));
  check_csrng_sw_state(&kat->state_instantiate);

  memcpy(seed.data, kat->seed_reseed1, sizeof(seed.data));
  CHECK_STATUS_OK(entropy_csrng_reseed(kHardenedBoolTrue, &seed));
  check_csrng_sw_state(&kat->state_reseed1);

  uint32_t got[16] = {0};
  CHECK_STATUS_OK(
      entropy_csrng_generate(NULL, got, ARRAYSIZE(got), kHardenedBoolFalse));
  check_csrng_sw_state(&kat->state_generate1);

  memcpy(seed.data, kat->seed_reseed2, sizeof(seed.data));
  CHECK_STATUS_OK(entropy_csrng_reseed(kHardenedBoolTrue, &seed));
  check_csrng_sw_state(&kat->state_reseed2);

  CHECK_STATUS_OK(
      entropy_csrng_generate(NULL, got, ARRAYSIZE(got), kHardenedBoolFalse));
  check_csrng_sw_state(&kat->state_generate2);
  CHECK_ARRAYS_EQ(got, kat->expected_output, ARRAYSIZE(got));

  CHECK_STATUS_OK(entropy_csrng_uninstantiate());
  return OK_STATUS();
}

// -----------------------------------------------------------------------------
// Main Test Entry Point
// -----------------------------------------------------------------------------

static status_t test_fips_kat_rom(void) {
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kDtAonTimer, &aon_timer));
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));

  const uintptr_t rom_base =
      dt_rom_ctrl_memory_base(kDtRomCtrlFirst, kDtRomCtrlMemoryRom);
  const size_t rom_size =
      dt_rom_ctrl_memory_size(kDtRomCtrlFirst, kDtRomCtrlMemoryRom);
  CHECK(rom_size >= kFipsKatRomEndOffset, "ROM too small for FIPS KAT window");
  const uintptr_t kat_base = rom_base + rom_size - kFipsKatRomEndOffset;

  // 1. Option B pre-map negative probes: default ROM_EXT handoff denies ROM.
  assert_load_faults(kat_base);
  assert_load_faults(rom_base);
  assert_load_faults(rom_base + rom_size - 0x20u);  // ECC-poisoned digest

  // 2. Transiently map [kat_base, kat_base + 32 KiB) as L=1, R=1 in slot 0.
  map_rom_kat_slot0(kat_base, kFipsKatRegionSize);

  // 3. During-map negative probes: W, X, and out-of-window accesses fault.
  assert_store_faults(kat_base);
  assert_exec_faults(kat_base);
  assert_load_faults(kat_base - 4u);
  assert_load_faults(kat_base + kFipsKatRegionSize);
  assert_load_faults(rom_base + rom_size - 0x20u);

  const fips_kat_descriptor_table_t *table =
      get_fips_descriptor_table_from_region((const void *)kat_base,
                                            kFipsKatRegionSize);
  CHECK(table != NULL, "Invalid ROM FIPS KAT descriptor table");
  CHECK(table->entry_count == 27u, "Expected 27 entries, got %u",
        table->entry_count);
  LOG_INFO("FIPS KAT table @ 0x%08x: %u entries, %u bytes (ePMP RO verified)",
           (uint32_t)kat_base, table->entry_count, table->total_size);

  // Initialize cryptolib once at High security level (alert checks enabled).
  CHECK_STATUS_OK(kmac_hwip_default_configure());
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelHigh));

  // Symmetric, Hash, MAC, KDF, and DRBG KATs.
  TRY(test_sha256_kat(table));
  TRY(test_sha512_kat(table));
  TRY(test_hmac_sha256_kat(table));
  TRY(test_hmac_sha512_kat(table));
  LOG_INFO("[1/6] SHA2 + HMAC ok");
  TRY(test_shake256_kat(table));
  TRY(test_kmac256_kat(table));
  TRY(test_aes_ecb256_kat(table));
  TRY(test_aes_cbc256_kat(table));
  TRY(test_aes_kwp256_kat(table));
  TRY(test_aes_gcm256_kat(table));
  LOG_INFO("[2/6] SHA3/KMAC + AES ok");
  TRY(test_kdf_hmac_sha256_kat(table));
  TRY(test_kdf_kmac256_kat(table));
  TRY(test_drbg_aes256_kat(table));
  LOG_INFO("[3/6] KDF + HKDF + DRBG ok");
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));

  // Classical Asymmetric KATs.
  TRY(test_rsa2048_verify_kat(table));
  TRY(test_rsa4096_sign_kat(table));
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));
  TRY(test_rsa4096_verify_kat(table));
  TRY(test_ecdsa_p256_sign_kat(table));
  TRY(test_ecdsa_p256_verify_kat(table));
  TRY(test_ecdsa_p384_sign_kat(table));
  TRY(test_ecdsa_p384_verify_kat(table));
  TRY(test_ed25519_sign_kat(table));
  TRY(test_ed25519_verify_kat(table));
  TRY(test_ecdh_p256_kat(table));
  TRY(test_ecdh_p384_kat(table));
  TRY(test_x25519_kat(table));
  LOG_INFO("[4/6] RSA + ECC ok");
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));

  // Post-Quantum KATs.
  TRY(test_sphincsplus_sha2_128s_verify_kat(table));
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));
  TRY(test_mldsa87_kat(table, &aon_timer));
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));
  LOG_INFO("[5/6] PQC (SPHINCS+/ML-DSA/ML-KEM) ok");
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));

  // 4. Immediately revoke transient ePMP mapping and verify ROM denies loads.
  unmap_rom_kat_slot0();
  assert_load_faults(kat_base);

  LOG_INFO("All 27 ROM FIPS KATs passed and transient ePMP revoked.");
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_fips_kat_rom();
  if (status_err(sts)) {
    LOG_ERROR("test_fips_kat_rom failed: %r", sts);
  }
  return status_ok(sts);
}
