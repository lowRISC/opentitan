// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_TESTVECTORS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_TESTVECTORS_H_

#include "sw/device/lib/crypto/include/aes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef struct aes_test {
  // Plaintext data.
  const uint32_t *plaintext;
  // Plaintext length in bytes.
  size_t plaintext_len;
  // Key data.
  const uint32_t *key;
  // Key length in bytes.
  size_t key_len;
  // IV data (always 16 bytes).
  const uint32_t *iv;
  // Padding mode.
  otcrypto_aes_padding_t padding;
  // Block cipher mode.
  otcrypto_aes_mode_t mode;
  // Expected ciphertext (length = same as #blocks in plaintext).
  const uint32_t *exp_ciphertext;
} aes_test_t;

static const size_t kPlaintextLen = 50;
static const uint32_t kPlaintext[13] = {
    0x238cc6b6, 0xd18458ba, 0x1df717b8, 0xdca42de3, 0x9b6397a7,
    0xe7ef81bb, 0x8b144a89, 0x09c78f90, 0x4a3cf3e0, 0x42985bb1,
    0x080baa3a, 0x7cb4ba1f, 0x0000a262,
};

// Length of plaintext for modes with no padding; cut off last word if it is
// incomplete.
static const size_t kPlaintextLenNoPadding =
    kPlaintextLen - (kPlaintextLen % sizeof(uint32_t));

static const uint32_t kIv[4] = {
    0x27e031b5,
    0x1ad7e548,
    0x99c07122,
    0xe1353f5b,
};

static const uint32_t kKey128[4] = {
    0x4e291d12,
    0x25492cbd,
    0xadf80531,
    0x9440ee26,
};

static const uint32_t kKey192[6] = {
    0x533b154d, 0xb3a32729, 0x12784d00, 0x5560457a, 0x0ec17ad8, 0x9a6f7317,
};

static const uint32_t kKey256[8] = {
    0x9079bf5d, 0x0d50e7c3, 0xda9a75ca, 0x91809c0e,
    0x677e6683, 0x45a72d11, 0x397fdeb9, 0xa39fc59f,
};

// Expected ciphertext for AES-ECB(kKey128, kIv, pad_pkcs7(kPlaintext))
static const uint32_t kEcb128Pkcs7[] = {
    0xd2fabbe1, 0x94e2f1ed, 0xc9b5e0f3, 0xba147a47, 0xd2060434, 0x295ecfeb,
    0x2cde404e, 0x924087c2, 0xee249f64, 0x5038956c, 0x5a4d9472, 0xabf934ce,
    0x7d742722, 0x1d879a45, 0x73e28a00, 0xdbc75cdc,
};

// Expected ciphertext for AES-CBC(kKey192, kIv, pad_iso9797m2(kPlaintext))
static const uint32_t kCbc192Iso9797M2[] = {
    0x48cdc584, 0x1848418a, 0x26fa1789, 0xf1d79c15, 0xa944ab10, 0x45f31abf,
    0xf6a89cb9, 0x869dad60, 0xfab29d9b, 0x30d07657, 0xbd466431, 0xc4fff0a5,
    0xa4240f83, 0x4cc42de1, 0x97e337b4, 0x4d58b7cc,
};

// Expected ciphertext for AES-CFB(kKey256, kIv, kPlaintext[:12])
static const uint32_t kCfb256Null[] = {
    0x3129e071, 0xdb2af89e, 0x8ea970a9, 0x3c71c28c, 0xae4ce122, 0x6d4b37d8,
    0xc0643e7e, 0x2e33b366, 0xef1837d2, 0x97a83277, 0xe36737c3, 0x4e918122,
};

// Expected ciphertext for AES-OFB(kKey192, kIv, pad_pkcs7(kPlaintext))
static const uint32_t kOfb192Pkcs7[] = {
    0x22045a08, 0xd4d55d0d, 0x23f94449, 0xc9878ac1, 0xce298265, 0xb52fbd05,
    0x9a11275a, 0xed2d5fb0, 0x6a4d1277, 0x5a4a94f2, 0xaea0b17f, 0x04bc087a,
    0x7e0641e2, 0xac13d179, 0xb9e026da, 0xbf3b492d,
};

// Expected ciphertext for AES-CTR(kKey256, kIv, pad_iso9797m2(kPlaintext))
static const uint32_t kCtr256Iso9797M2[] = {
    0x3129e071, 0xdb2af89e, 0x8ea970a9, 0x3c71c28c, 0xfd2450bd, 0x87dd491c,
    0x8d3c4cb3, 0x8a36762,  0xc58604da, 0xe8fe81b6, 0x92ae20cc, 0x2a037d00,
    0xf7381cce, 0xff605215, 0x1bf3cf3d, 0x9d5935c,
};

static const aes_test_t kAesTests[] = {
    // ECB, 128-bit key, PKCS#7 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey128,
        .key_len = sizeof(kKey128),
        .padding = kOtcryptoAesPaddingPkcs7,
        .mode = kOtcryptoAesModeEcb,
        .exp_ciphertext = kEcb128Pkcs7,
    },
    // CBC, 192-bit key, ISO9797-2 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey192,
        .key_len = sizeof(kKey192),
        .padding = kOtcryptoAesPaddingIso9797M2,
        .mode = kOtcryptoAesModeCbc,
        .exp_ciphertext = kCbc192Iso9797M2,
    },
    // CFB, 256-bit key, no padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLenNoPadding,
        .iv = kIv,
        .key = kKey256,
        .key_len = sizeof(kKey256),
        .padding = kOtcryptoAesPaddingNull,
        .mode = kOtcryptoAesModeCfb,
        .exp_ciphertext = kCfb256Null,
    },
    // OFB, 192-bit key, PKCS#7 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey192,
        .key_len = sizeof(kKey192),
        .padding = kOtcryptoAesPaddingPkcs7,
        .mode = kOtcryptoAesModeOfb,
        .exp_ciphertext = kOfb192Pkcs7,
    },
    // CTR, 256-bit key, ISO9797-2 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey256,
        .key_len = sizeof(kKey256),
        .padding = kOtcryptoAesPaddingIso9797M2,
        .mode = kOtcryptoAesModeCtr,
        .exp_ciphertext = kCtr256Iso9797M2,
    },
};

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_AES_TESTVECTORS_H_
