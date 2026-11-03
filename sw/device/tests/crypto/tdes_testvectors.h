// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_TDES_TESTVECTORS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_TDES_TESTVECTORS_H_

#include "sw/device/lib/crypto/include/tdes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef struct tdes_test {
  // Plaintext data.
  const uint32_t *plaintext;
  // Plaintext length in bytes.
  size_t plaintext_len;
  // Key data.
  const uint32_t *key;
  // Key length in bytes.
  size_t key_len;
  // IV data (always 8 bytes).
  const uint32_t *iv;
  // Padding mode.
  otcrypto_tdes_padding_t padding;
  // Block cipher mode.
  otcrypto_tdes_mode_t mode;
  // Expected ciphertext (length = same as #blocks in padded plaintext).
  const uint32_t *exp_ciphertext;
} tdes_test_t;

static const size_t kPlaintextLen = 50;
static const uint32_t kPlaintext[13] = {
    0x238cc6b6, 0xd18458ba, 0x1df717b8, 0xdca42de3, 0x9b6397a7,
    0xe7ef81bb, 0x8b144a89, 0x09c78f90, 0x4a3cf3e0, 0x42985bb1,
    0x080baa3a, 0x7cb4ba1f, 0x0000a262,
};

// Length of plaintext for modes with no padding (multiple of 8-byte block).
static const size_t kPlaintextLenNoPadding = 48;

static const uint32_t kIv[2] = {
    0x27e031b5,
    0x1ad7e548,
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

// Packed 168-bit (21-byte) 3-key TDES key equivalent to kKey192 without parity
// bits.
static const size_t kKey168PackedLen = 21;
static const uint32_t kKey168Packed[6] = {
    0x92ea284c, 0x00d9e884, 0xa897e099, 0xf7d82a98, 0x5b6e7100, 0x000000cd,
};

// Expected ciphertext for TDES-ECB(kKey128, kIv, pad_pkcs7(kPlaintext))
static const uint32_t kEcb128Pkcs7[] = {
    0x67d6cfee, 0x32b3d423, 0x3b7cd772, 0x21066ffd, 0x56abfce3,
    0x7c77d987, 0x41eebfea, 0x606ac2bf, 0x1d62e506, 0xc791cde7,
    0x03a3b50c, 0xb27b15d9, 0x13d7c8a7, 0xa607231c,
};

// Expected ciphertext for TDES-CBC(kKey192, kIv, pad_iso9797m2(kPlaintext))
static const uint32_t kCbc192Iso9797M2[] = {
    0xaf152b1e, 0x56d78f87, 0x684f2349, 0x5a2fec4a, 0xa2da12a6,
    0x2a8ca06a, 0x55bc8401, 0xb92d50c1, 0xfb56136a, 0xc74899d2,
    0xc5e2492b, 0xf7bf70ab, 0xb0a7c373, 0x93664d94,
};

// Expected ciphertext for TDES-CFB(kKey192, kIv, kPlaintext[:12])
static const uint32_t kCfb192Null[] = {
    0xb7b79e5d, 0x68de925b, 0xa3e1a32c, 0x1e6e4792, 0xfd10f3f3, 0x419ca229,
    0x4fbbe666, 0x1ec5b416, 0x42dbaa3b, 0xd223893d, 0xf49ce522, 0xd4dcc5ab,
};

// Expected ciphertext for TDES-OFB(kKey128, kIv, pad_pkcs7(kPlaintext))
static const uint32_t kOfb128Pkcs7[] = {
    0xc43d32ff, 0x31f1a0af, 0xcfb2b5be, 0x7b316adb, 0x98fbb018,
    0xfa5d5d8f, 0x146714e9, 0x626ae559, 0x19f76c50, 0x79eb33d3,
    0x2de571bc, 0xa4724e80, 0x985ccefd, 0xecefae4c,
};

// Expected ciphertext for TDES-CTR(kKey192, kIv, pad_iso9797m2(kPlaintext))
static const uint32_t kCtr192Iso9797M2[] = {
    0xb7b79e5d, 0x68de925b, 0xbab1e811, 0xfa5ceabe, 0xe8bc34e2,
    0x6af29bd2, 0x88f0d419, 0x20b58033, 0xc2b024a4, 0x5c17bed3,
    0x84497c14, 0x9e81bf7a, 0xbe0d8c11, 0xc2cceef5,
};

static const tdes_test_t kTdesTests[] = {
    // ECB, 128-bit (2-key) key, PKCS#7 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey128,
        .key_len = sizeof(kKey128),
        .padding = kOtcryptoTdesPaddingPkcs7,
        .mode = kOtcryptoTdesModeEcb,
        .exp_ciphertext = kEcb128Pkcs7,
    },
    // CBC, 192-bit (3-key) key, ISO9797-2 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey192,
        .key_len = sizeof(kKey192),
        .padding = kOtcryptoTdesPaddingIso9797M2,
        .mode = kOtcryptoTdesModeCbc,
        .exp_ciphertext = kCbc192Iso9797M2,
    },
    // CFB, 192-bit (3-key) key, no padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLenNoPadding,
        .iv = kIv,
        .key = kKey192,
        .key_len = sizeof(kKey192),
        .padding = kOtcryptoTdesPaddingNull,
        .mode = kOtcryptoTdesModeCfb,
        .exp_ciphertext = kCfb192Null,
    },
    // OFB, 128-bit (2-key) key, PKCS#7 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey128,
        .key_len = sizeof(kKey128),
        .padding = kOtcryptoTdesPaddingPkcs7,
        .mode = kOtcryptoTdesModeOfb,
        .exp_ciphertext = kOfb128Pkcs7,
    },
    // CTR, 192-bit (3-key) key, ISO9797-2 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey192,
        .key_len = sizeof(kKey192),
        .padding = kOtcryptoTdesPaddingIso9797M2,
        .mode = kOtcryptoTdesModeCtr,
        .exp_ciphertext = kCtr192Iso9797M2,
    },
    // CBC, 168-bit (21-byte packed 3-key) key, ISO9797-2 padding
    {
        .plaintext = kPlaintext,
        .plaintext_len = kPlaintextLen,
        .iv = kIv,
        .key = kKey168Packed,
        .key_len = kKey168PackedLen,
        .padding = kOtcryptoTdesPaddingIso9797M2,
        .mode = kOtcryptoTdesModeCbc,
        .exp_ciphertext = kCbc192Iso9797M2,
    },
};

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_TDES_TESTVECTORS_H_
