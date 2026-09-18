// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/hkdf.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/hkdf_commands.h"

static const uint32_t kTestMask[32] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e, 0x8cb847c3,
    0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049, 0xfd463b63,
    0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345, 0xa7ebc3e3,
    0x04b2a1b9, 0x764a9630,
};

status_t handle_hkdf(ujson_t *uj) {
  cryptotest_hkdf_hash_alg_t uj_hash_alg;
  cryptotest_hkdf_data_t uj_data;
  TRY(ujson_deserialize_cryptotest_hkdf_hash_alg_t(uj, &uj_hash_alg));
  TRY(ujson_deserialize_cryptotest_hkdf_data_t(uj, &uj_data));

  otcrypto_key_mode_t key_mode;
  size_t digest_words;
  switch (uj_hash_alg) {
    case kCryptotestHkdfHashAlgSha256:
      key_mode = kOtcryptoKeyModeHmacSha256;
      digest_words = 8;
      break;
    case kCryptotestHkdfHashAlgSha384:
      key_mode = kOtcryptoKeyModeHmacSha384;
      digest_words = 12;
      break;
    case kCryptotestHkdfHashAlgSha512:
      key_mode = kOtcryptoKeyModeHmacSha512;
      digest_words = 16;
      break;
    default:
      return INVALID_ARGUMENT();
  }

  cryptotest_hkdf_okm_t uj_okm;
  memset(&uj_okm, 0, sizeof(uj_okm));

  size_t okm_wordlen = ceil_div(uj_data.okm_len, sizeof(uint32_t));
  (void)digest_words;

  otcrypto_key_config_t ikm_config = {
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
      .key_length = uj_data.ikm_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t ikm_aligned[32];
  memset(ikm_aligned, 0, sizeof(ikm_aligned));
  if (uj_data.ikm_len > 0) {
    memcpy(ikm_aligned, uj_data.ikm, uj_data.ikm_len);
  }
  uint32_t ikm_keyblob[64];
  TRY(keyblob_from_key_and_mask(ikm_aligned, kTestMask, ikm_config,
                                ikm_keyblob));
  otcrypto_blinded_key_t ikm = {
      .config = ikm_config,
      .keyblob = ikm_keyblob,
      .keyblob_length = keyblob_num_words(ikm_config) * sizeof(uint32_t),
  };
  ikm.checksum = otcrypto_integrity_blinded_checksum(&ikm);

  otcrypto_key_config_t okm_config = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = uj_data.okm_len,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  size_t okm_alloc_words =
      okm_wordlen <= (HKDF_CMD_MAX_OKM_BYTES / sizeof(uint32_t))
          ? (okm_wordlen > 0 ? okm_wordlen : 1)
          : (HKDF_CMD_MAX_OKM_BYTES / sizeof(uint32_t));
  uint32_t okm_keyblob[2 * okm_alloc_words];
  otcrypto_blinded_key_t okm = {
      .config = okm_config,
      .keyblob = okm_keyblob,
      .keyblob_length = keyblob_num_words(okm_config) * sizeof(uint32_t),
  };

  otcrypto_const_byte_buf_t salt = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_data.salt_len > 0 ? uj_data.salt : NULL,
      uj_data.salt_len);
  otcrypto_const_byte_buf_t info = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, uj_data.info_len > 0 ? uj_data.info : NULL,
      uj_data.info_len);

  otcrypto_status_t status = otcrypto_hkdf(&ikm, &salt, &info, &okm);
  if (status.value != kOtcryptoStatusValueOk) {
    uj_okm.status_ok = false;
    RESP_OK(ujson_serialize_cryptotest_hkdf_okm_t, uj, &uj_okm);
    return OK_STATUS(0);
  }

  uint32_t *okm_share0;
  uint32_t *okm_share1;
  TRY(keyblob_to_shares(&okm, &okm_share0, &okm_share1));
  uint32_t unmasked_okm[okm_alloc_words];
  for (size_t i = 0; i < okm_alloc_words; i++) {
    unmasked_okm[i] = okm_share0[i] ^ okm_share1[i];
  }
  memcpy(uj_okm.okm, unmasked_okm, uj_data.okm_len);
  uj_okm.okm_len = uj_data.okm_len;
  uj_okm.status_ok = true;

  RESP_OK(ujson_serialize_cryptotest_hkdf_okm_t, uj, &uj_okm);
  return OK_STATUS(0);
}
