// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "hw/top/dt/aon_timer.h"
#include "hw/top/dt/hmac.h"
#include "hw/top/dt/kmac.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include "hw/top/aes_regs.h"
#include "hw/top/hmac_regs.h"

OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

static const uint8_t __attribute__((unused)) kExpectedSha256Digest[32] = {
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40,
    0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17,
    0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};

static const uint8_t __attribute__((unused)) kExpectedHmacSha256Digest[32] = {
    0xcd, 0xcb, 0x12, 0x20, 0xd1, 0xec, 0xcc, 0xea, 0x91, 0xe5, 0x3a,
    0xba, 0x30, 0x92, 0xf9, 0x62, 0xe5, 0x49, 0xfe, 0x6c, 0xe9, 0xed,
    0x7f, 0xdc, 0x43, 0x19, 0x1f, 0xbd, 0xe4, 0x5c, 0x30, 0xb0,
};

static const uint8_t __attribute__((unused)) kExpectedSha512Digest[64] = {
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73,
    0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9,
    0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21,
    0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23,
    0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8,
    0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
};

static const uint8_t __attribute__((unused)) kExpectedHmacSha512Digest[64] = {
    0xfa, 0x73, 0xb0, 0x08, 0x9d, 0x56, 0xa2, 0x84, 0xef, 0xb0, 0xf0,
    0x75, 0x6c, 0x89, 0x0b, 0xe9, 0xb1, 0xb5, 0xdb, 0xdd, 0x8e, 0xe8,
    0x1a, 0x36, 0x55, 0xf8, 0x3e, 0x33, 0xb2, 0x27, 0x9d, 0x39, 0xbf,
    0x3e, 0x84, 0x82, 0x79, 0xa7, 0x22, 0xc8, 0x06, 0xb4, 0x85, 0xa4,
    0x7e, 0x67, 0xc8, 0x07, 0xb9, 0x46, 0xa3, 0x37, 0xbe, 0xe8, 0x94,
    0x26, 0x74, 0x27, 0x88, 0x59, 0xe1, 0x32, 0x92, 0xfb,
};

static const uint8_t __attribute__((unused)) kExpectedAes256Key[32] = {
    0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae,
    0xf0, 0x85, 0x7d, 0x77, 0x81, 0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61,
    0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4,
};

static const uint8_t __attribute__((unused)) kExpectedAes256EcbPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes256EcbCt[16] = {
    0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c,
    0x06, 0x4b, 0x5a, 0x7e, 0x3d, 0xb1, 0x81, 0xf8,
};

static const uint8_t __attribute__((unused)) kExpectedAes128Key[16] = {
    0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
    0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
};

static const uint8_t __attribute__((unused)) kExpectedAes128EcbPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes128EcbCt[16] = {
    0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60,
    0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcIv[16] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcCt[16] = {
    0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba,
    0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6,
};

static const uint8_t __attribute__((unused)) kExpectedAes128CbcIv[16] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static const uint8_t __attribute__((unused)) kExpectedAes128CbcPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes128CbcCt[16] = {
    0x76, 0x49, 0xab, 0xac, 0x81, 0x19, 0xb2, 0x46,
    0xce, 0xe9, 0x8e, 0x9b, 0x12, 0xe9, 0x19, 0x7d,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Kdk[32] = {
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Msg[21] = {
    0x00, 0x00, 0x00, 0x01, 0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0x00,
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x00, 0x00, 0x01, 0x00,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Km[32] = {
    0x12, 0xb4, 0x4b, 0x70, 0x02, 0x76, 0xc0, 0x30, 0x74, 0xcd, 0x99,
    0xf9, 0x87, 0x63, 0x57, 0x4b, 0x7b, 0xf7, 0x1c, 0x30, 0x34, 0x02,
    0x23, 0x79, 0x0b, 0xf0, 0xb8, 0xf5, 0x3f, 0xcf, 0x3c, 0x86,
};

static const uint8_t __attribute__((unused)) kExpectedShake256Msg[1] = {0x0f};

static const uint8_t __attribute__((unused)) kExpectedShake256Digest[32] = {
    0xaa, 0xbb, 0x07, 0x48, 0x8f, 0xf9, 0xed, 0xd0, 0x5d, 0x6a, 0x60,
    0x3b, 0x77, 0x91, 0xb6, 0x0a, 0x16, 0xd4, 0x50, 0x93, 0x60, 0x8f,
    0x1b, 0xad, 0xc0, 0xc9, 0xcc, 0x9a, 0x91, 0x54, 0xf2, 0x15,
};

static const uint8_t __attribute__((unused)) kExpectedKmac256Key[32] = {
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a,
    0x4b, 0x4c, 0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,
    0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
};

static const uint8_t
    __attribute__((unused)) kExpectedKmac256Msg[4] = {0x00, 0x01, 0x02, 0x03};

static const uint8_t __attribute__((unused)) kExpectedKmac256Digest[64] = {
    0x20, 0xc5, 0x70, 0xc3, 0x13, 0x46, 0xf7, 0x03, 0xc9, 0xac, 0x36,
    0xc6, 0x1c, 0x03, 0xcb, 0x64, 0xc3, 0x97, 0x0d, 0x0c, 0xfc, 0x78,
    0x7e, 0x9b, 0x79, 0x59, 0x9d, 0x27, 0x3a, 0x68, 0xd2, 0xf7, 0xf6,
    0x9d, 0x4c, 0xc3, 0xde, 0x9d, 0x10, 0x4a, 0x35, 0x16, 0x89, 0xf2,
    0x7c, 0xf6, 0xf5, 0x95, 0x1f, 0x01, 0x03, 0xf3, 0x3f, 0x4f, 0x24,
    0x87, 0x10, 0x24, 0xd9, 0xc2, 0x77, 0x73, 0xa8, 0xdd,
};

static const uint8_t __attribute__((unused)) kExpectedKmac128Key[32] = {
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a,
    0x4b, 0x4c, 0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,
    0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
};

static const uint8_t
    __attribute__((unused)) kExpectedKmac128Msg[4] = {0x00, 0x01, 0x02, 0x03};

static const uint8_t __attribute__((unused)) kExpectedKmac128Digest[32] = {
    0xe5, 0x78, 0x0b, 0x0d, 0x3e, 0xa6, 0xf7, 0xd3, 0xa4, 0x29, 0xc5,
    0x70, 0x6a, 0xa4, 0x3a, 0x00, 0xfa, 0xdb, 0xd7, 0xd4, 0x96, 0x28,
    0x83, 0x9e, 0x31, 0x87, 0x24, 0x3f, 0x45, 0x6e, 0xe1, 0x4e,
};

static const uint8_t __attribute__((unused)) kExpectedAesKwp256Ct[24] = {
    0xcc, 0x06, 0xca, 0x9e, 0xd0, 0x8d, 0xb0, 0x32, 0x13, 0x48, 0x1e, 0x0b,
    0x44, 0x0d, 0x7f, 0xab, 0xf8, 0x85, 0x0c, 0xcc, 0xad, 0x63, 0x00, 0x53,
};

static const uint8_t __attribute__((unused)) kExpectedAesKwp128Ct[24] = {
    0xe1, 0x7d, 0xaa, 0x13, 0x0c, 0xf8, 0xbc, 0xa1, 0x64, 0x39, 0x01, 0xa5,
    0x8d, 0x28, 0xe7, 0x99, 0x43, 0x2d, 0x78, 0x48, 0xde, 0x59, 0xb3, 0x4d,
};

static status_t test_sha256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SHA2-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgSha2_256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgSha2_256);
  CHECK(entry != NULL, "SHA2-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SHA2-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 0, "Expected key_len=0, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 3, "Expected msg_len=3, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *msg = kat_data->data;
  const uint8_t *expected_digest = kat_data->data + kat_data->msg_len;

  CHECK(msg[0] == 'a' && msg[1] == 'b' && msg[2] == 'c',
        "Test vector message mismatch!");
  CHECK_ARRAYS_EQ(expected_digest, kExpectedSha256Digest, 32);
  LOG_INFO("SHA2-256 vector payload verified against golden values.");

  LOG_INFO("Executing SHA2-256 hash using HMAC hardware accelerator...");
  hmac_digest_t digest;
  hmac_sha256(msg, kat_data->msg_len, &digest);

  // Convert little-endian word digest from hmac_sha256 to big-endian byte
  // array.
  uint8_t computed_digest[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t word = digest.digest[7 - i];
    computed_digest[4 * i] = (uint8_t)(word >> 24);
    computed_digest[4 * i + 1] = (uint8_t)(word >> 16);
    computed_digest[4 * i + 2] = (uint8_t)(word >> 8);
    computed_digest[4 * i + 3] = (uint8_t)(word);
  }

  CHECK_ARRAYS_EQ(computed_digest, expected_digest, 32);
  LOG_INFO("SHA2-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_hmac_sha256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for HMAC-SHA2-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgHmacSha2_256);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgHmacSha2_256);
  CHECK(entry != NULL, "HMAC-SHA2-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving HMAC-SHA2-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 50, "Expected msg_len=50, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  for (size_t i = 0; i < 32; ++i) {
    CHECK(key[i] == 0xaa, "Key byte %zu mismatch: expected 0xaa, got 0x%02x", i,
          key[i]);
  }
  for (size_t i = 0; i < 50; ++i) {
    CHECK(msg[i] == 0xdd, "Msg byte %zu mismatch: expected 0xdd, got 0x%02x", i,
          msg[i]);
  }
  CHECK_ARRAYS_EQ(expected_digest, kExpectedHmacSha256Digest, 32);
  LOG_INFO("HMAC-SHA2-256 vector payload verified against golden values.");

  LOG_INFO("Executing HMAC-SHA2-256 using HMAC hardware accelerator...");
  hmac_key_t hkey;
  for (size_t i = 0; i < 8; ++i) {
    hkey.key[i] = (uint32_t)key[4 * i] | ((uint32_t)key[4 * i + 1] << 8) |
                  ((uint32_t)key[4 * i + 2] << 16) |
                  ((uint32_t)key[4 * i + 3] << 24);
  }
  hmac_digest_t digest;
  sc_hmac_hmac_sha256(msg, kat_data->msg_len, hkey, /*big_endian_digest=*/false,
                      &digest);

  uint8_t computed_digest[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t word = digest.digest[7 - i];
    computed_digest[4 * i] = (uint8_t)(word >> 24);
    computed_digest[4 * i + 1] = (uint8_t)(word >> 16);
    computed_digest[4 * i + 2] = (uint8_t)(word >> 8);
    computed_digest[4 * i + 3] = (uint8_t)(word);
  }

  CHECK_ARRAYS_EQ(computed_digest, expected_digest, 32);
  LOG_INFO("HMAC-SHA2-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_sha512_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SHA2-512 KAT entry (alg_id = %u)...",
           kFipsKatAlgSha2_512);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgSha2_512);
  CHECK(entry != NULL, "SHA2-512 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SHA2-512 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 0, "Expected key_len=0, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 3, "Expected msg_len=3, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  CHECK(msg[0] == 'a' && msg[1] == 'b' && msg[2] == 'c',
        "Test vector message mismatch!");
  CHECK_ARRAYS_EQ(expected_digest, kExpectedSha512Digest, 64);
  LOG_INFO("SHA2-512 vector payload verified against golden values.");

  LOG_INFO("Executing SHA2-512 hash using HMAC hardware accelerator...");
  const uint32_t hmac_base_addr = dt_hmac_primary_reg_block(kDtHmac);

  // Clear config and disable interrupts
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, UINT32_MAX);

  // Configure HMAC IP for SHA2-512 with digest_swap = true
  uint32_t cfg = 0;
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, false);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_NONE);
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, cfg);

  // Start hash
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, true));

  // Write message bytes into FIFO
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    abs_mmio_write8(hmac_base_addr + HMAC_MSG_FIFO_REG_OFFSET, msg[i]);
  }

  // Trigger process
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_PROCESS_BIT, true));

  // Wait until hmac_done interrupt flag is asserted
  uint32_t intr_state = 0;
  do {
    intr_state = abs_mmio_read32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, intr_state);

  // Read 16 digest registers (64 bytes)
  uint32_t computed_digest[16];
  for (size_t i = 0; i < 16; ++i) {
    computed_digest[i] = abs_mmio_read32(
        hmac_base_addr + HMAC_DIGEST_0_REG_OFFSET + i * sizeof(uint32_t));
  }

  CHECK_ARRAYS_EQ((const uint8_t *)computed_digest, expected_digest, 64);
  LOG_INFO("SHA2-512 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_hmac_sha512_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for HMAC-SHA2-512 KAT entry (alg_id = %u)...",
           kFipsKatAlgHmacSha2_512);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgHmacSha2_512);
  CHECK(entry != NULL, "HMAC-SHA2-512 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving HMAC-SHA2-512 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 20, "Expected key_len=20, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 50, "Expected msg_len=50, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  for (size_t i = 0; i < kat_data->key_len; ++i) {
    CHECK(key[i] == 0xaa, "Key byte %zu mismatch: expected 0xaa, got 0x%02x", i,
          key[i]);
  }
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    CHECK(msg[i] == 0xdd, "Msg byte %zu mismatch: expected 0xdd, got 0x%02x", i,
          msg[i]);
  }
  CHECK_ARRAYS_EQ(expected_digest, kExpectedHmacSha512Digest, 64);
  LOG_INFO("HMAC-SHA2-512 vector payload verified against golden values.");

  LOG_INFO("Executing HMAC-SHA2-512 using HMAC hardware accelerator...");
  const uint32_t hmac_base_addr = dt_hmac_primary_reg_block(kDtHmac);

  // Clear config and disable interrupts
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, UINT32_MAX);

  // Configure HMAC IP for HMAC-SHA2-512 with 1024-bit key block
  uint32_t cfg = 0;
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_KEY_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, true);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_1024);
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, cfg);

  // Write 1024-bit key block (padded with zeros)
  uint32_t key_block[32] = {0};
  memcpy(key_block, key, kat_data->key_len);
  for (size_t i = 0; i < 32; ++i) {
    abs_mmio_write32(
        hmac_base_addr + HMAC_KEY_0_REG_OFFSET + i * sizeof(uint32_t),
        key_block[i]);
  }

  // Start hash
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, true));

  // Write message bytes into FIFO
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    abs_mmio_write8(hmac_base_addr + HMAC_MSG_FIFO_REG_OFFSET, msg[i]);
  }

  // Trigger process
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_PROCESS_BIT, true));

  // Wait until hmac_done interrupt flag is asserted
  uint32_t intr_state = 0;
  do {
    intr_state = abs_mmio_read32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, intr_state);

  // Read 16 digest registers (64 bytes)
  uint32_t computed_digest[16];
  for (size_t i = 0; i < 16; ++i) {
    computed_digest[i] = abs_mmio_read32(
        hmac_base_addr + HMAC_DIGEST_0_REG_OFFSET + i * sizeof(uint32_t));
  }

  CHECK_ARRAYS_EQ((const uint8_t *)computed_digest, expected_digest, 64);
  LOG_INFO("HMAC-SHA2-512 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_fips_kat_rom(void) {
  // Stop the watchdog timer to prevent timeout during long RSA-4096 OTBN
  // computations.
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kDtAonTimer, &aon_timer));
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));

  LOG_INFO("Reading FIPS KAT descriptor table from ROM...");
  const fips_kat_descriptor_table_t *table = get_fips_descriptor_table();
  CHECK(table != NULL, "FIPS KAT table pointer is NULL!");
  CHECK(table->magic == kFipsKatDescriptorMagic, "Invalid table magic: 0x%08x",
        table->magic);
  CHECK(table->version == kFipsKatDescriptorVersion1,
        "Invalid table version: %u", table->version);
  CHECK(table->entry_count >= 4, "Expected at least 4 entries, got %u",
        table->entry_count);
  LOG_INFO(
      "FIPS KAT table found at %p (magic=0x%08x, version=%u, entries=%u, "
      "total_size=%u)",
      table, table->magic, table->version, table->entry_count,
      table->total_size);

  TRY(test_sha256_kat(table));
  TRY(test_hmac_sha256_kat(table));
  TRY(test_sha512_kat(table));
  TRY(test_hmac_sha512_kat(table));

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_fips_kat_rom();
  if (status_err(sts)) {
    LOG_ERROR("test_fips_kat_rom failed: %r", sts);
  }
  return status_ok(sts);
}
