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
  CHECK(table->entry_count == 6u, "Expected 6 entries, got %u",
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
  LOG_INFO("[2/6] SHA3/KMAC + AES ok");
  CHECK_DIF_OK(dif_aon_timer_watchdog_pet(&aon_timer));

  // 4. Immediately revoke transient ePMP mapping and verify ROM denies loads.
  unmap_rom_kat_slot0();
  assert_load_faults(kat_base);

  LOG_INFO("All 6 ROM FIPS KATs passed and transient ePMP revoked.");
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_fips_kat_rom();
  if (status_err(sts)) {
    LOG_ERROR("test_fips_kat_rom failed: %r", sts);
  }
  return status_ok(sts);
}
