// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/kats.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy_kat.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/kmac.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"

// We first provide all configs and test vectors
static const uint32_t kTestMask[] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

// FIPS 180-4 SHA Test Vectors for Hashing Byte-Oriented Messages SHA-256
// ShortMsg Len = 8 Msg = d3 MD =
// 28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1
static const uint8_t sha256_in[] = {0xd3};

static const uint8_t sha256_ans[32] = {
    0x28, 0x96, 0x9c, 0xdf, 0xa7, 0x4a, 0x12, 0xc8, 0x2f, 0x3b, 0xad,
    0x96, 0x0b, 0x0b, 0x00, 0x0a, 0xca, 0x2a, 0xc3, 0x29, 0xde, 0xea,
    0x5c, 0x23, 0x28, 0xeb, 0xc6, 0xf2, 0xba, 0x98, 0x02, 0xc1};

// HMAC CAVP L=32
// Count = 0
// Klen = 40
// Tlen = 16
// Key =
// 6f35628d65813435534b5d67fbdb54cb33403d04e843103e6399f806cb5df95febbdd61236f33245
// Msg =
// 752cff52e4b90768558e5369e75d97c69643509a5e5904e0a386cbe4d0970ef73f918f675945a9aefe26daea27587e8dc909dd56fd0468805f834039b345f855cfe19c44b55af241fff3ffcd8045cd5c288e6c4e284c3720570b58e4d47b8feeedc52fd1401f698a209fccfa3b4c0d9a797b046a2759f82a54c41ccd7b5f592b
// Mac = 05d1243e6465ed9620c9aec1c351a186

static const otcrypto_key_config_t kSha256Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeHmacSha256,
    .key_length = 40,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint8_t hmac_sha256_key[40] = {
    0x6f, 0x35, 0x62, 0x8d, 0x65, 0x81, 0x34, 0x35, 0x53, 0x4b,
    0x5d, 0x67, 0xfb, 0xdb, 0x54, 0xcb, 0x33, 0x40, 0x3d, 0x04,
    0xe8, 0x43, 0x10, 0x3e, 0x63, 0x99, 0xf8, 0x06, 0xcb, 0x5d,
    0xf9, 0x5f, 0xeb, 0xbd, 0xd6, 0x12, 0x36, 0xf3, 0x32, 0x45};

static const uint8_t hmac_sha256_in[128] = {
    0x75, 0x2c, 0xff, 0x52, 0xe4, 0xb9, 0x07, 0x68, 0x55, 0x8e, 0x53, 0x69,
    0xe7, 0x5d, 0x97, 0xc6, 0x96, 0x43, 0x50, 0x9a, 0x5e, 0x59, 0x04, 0xe0,
    0xa3, 0x86, 0xcb, 0xe4, 0xd0, 0x97, 0x0e, 0xf7, 0x3f, 0x91, 0x8f, 0x67,
    0x59, 0x45, 0xa9, 0xae, 0xfe, 0x26, 0xda, 0xea, 0x27, 0x58, 0x7e, 0x8d,
    0xc9, 0x09, 0xdd, 0x56, 0xfd, 0x04, 0x68, 0x80, 0x5f, 0x83, 0x40, 0x39,
    0xb3, 0x45, 0xf8, 0x55, 0xcf, 0xe1, 0x9c, 0x44, 0xb5, 0x5a, 0xf2, 0x41,
    0xff, 0xf3, 0xff, 0xcd, 0x80, 0x45, 0xcd, 0x5c, 0x28, 0x8e, 0x6c, 0x4e,
    0x28, 0x4c, 0x37, 0x20, 0x57, 0x0b, 0x58, 0xe4, 0xd4, 0x7b, 0x8f, 0xee,
    0xed, 0xc5, 0x2f, 0xd1, 0x40, 0x1f, 0x69, 0x8a, 0x20, 0x9f, 0xcc, 0xfa,
    0x3b, 0x4c, 0x0d, 0x9a, 0x79, 0x7b, 0x04, 0x6a, 0x27, 0x59, 0xf8, 0x2a,
    0x54, 0xc4, 0x1c, 0xcd, 0x7b, 0x5f, 0x59, 0x2b};

static const uint8_t hmac_sha256_ans[16] = {0x05, 0xd1, 0x24, 0x3e, 0x64, 0x65,
                                            0xed, 0x96, 0x20, 0xc9, 0xae, 0xc1,
                                            0xc3, 0x51, 0xa1, 0x86};

// FIPS 180-4 SHA Test Vectors for Hashing Byte-Oriented Messages SHA-512
// ShortMsg Len = 8 Msg = 21 MD =
// 3831a6a6155e509dee59a7f451eb35324d8f8f2df6e3708894740f98fdee23889f4de5adb0c5010dfb555cda77c8ab5dc902094c52de3278f35a75ebc25f093a
static const uint8_t sha512_in[] = {0x21};

static const uint8_t sha512_ans[64] = {
    0x38, 0x31, 0xa6, 0xa6, 0x15, 0x5e, 0x50, 0x9d, 0xee, 0x59, 0xa7,
    0xf4, 0x51, 0xeb, 0x35, 0x32, 0x4d, 0x8f, 0x8f, 0x2d, 0xf6, 0xe3,
    0x70, 0x88, 0x94, 0x74, 0x0f, 0x98, 0xfd, 0xee, 0x23, 0x88, 0x9f,
    0x4d, 0xe5, 0xad, 0xb0, 0xc5, 0x01, 0x0d, 0xfb, 0x55, 0x5c, 0xda,
    0x77, 0xc8, 0xab, 0x5d, 0xc9, 0x02, 0x09, 0x4c, 0x52, 0xde, 0x32,
    0x78, 0xf3, 0x5a, 0x75, 0xeb, 0xc2, 0x5f, 0x09, 0x3a};

// HMAC CAVP L=64
// Count = 0
// Klen = 100
// Tlen = 32
// Key =
// 726374c4b8df517510db9159b730f93431e0cd468d4f3821eab0edb93abd0fba46ab4f1ef35d54fec3d85fa89ef72ff3d35f22cf5ab69e205c10afcdf4aaf11338dbb12073474fddb556e60b8ee52f91163ba314303ee0c910e64e87fbf302214edbe3f2
// Msg =
// ac939659dc5f668c9969c0530422e3417a462c8b665e8db25a883a625f7aa59b89c5ad0ece5712ca17442d1798c6dea25d82c5db260cb59c75ae650be56569c1bd2d612cc57e71315917f116bbfa65a0aeb8af7840ee83d3e7101c52cf652d2773531b7a6bdd690b846a741816c860819270522a5b0cdfa1d736c501c583d916
// Mac = bd3d2df6f9d284b421a43e5f9cb94bc4ff88a88243f1f0133bad0fb1791f6569

static const otcrypto_key_config_t kSha512Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeHmacSha512,
    .key_length = 100,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint8_t hmac_sha512_key[100] = {
    0x72, 0x63, 0x74, 0xc4, 0xb8, 0xdf, 0x51, 0x75, 0x10, 0xdb, 0x91, 0x59,
    0xb7, 0x30, 0xf9, 0x34, 0x31, 0xe0, 0xcd, 0x46, 0x8d, 0x4f, 0x38, 0x21,
    0xea, 0xb0, 0xed, 0xb9, 0x3a, 0xbd, 0x0f, 0xba, 0x46, 0xab, 0x4f, 0x1e,
    0xf3, 0x5d, 0x54, 0xfe, 0xc3, 0xd8, 0x5f, 0xa8, 0x9e, 0xf7, 0x2f, 0xf3,
    0xd3, 0x5f, 0x22, 0xcf, 0x5a, 0xb6, 0x9e, 0x20, 0x5c, 0x10, 0xaf, 0xcd,
    0xf4, 0xaa, 0xf1, 0x13, 0x38, 0xdb, 0xb1, 0x20, 0x73, 0x47, 0x4f, 0xdd,
    0xb5, 0x56, 0xe6, 0x0b, 0x8e, 0xe5, 0x2f, 0x91, 0x16, 0x3b, 0xa3, 0x14,
    0x30, 0x3e, 0xe0, 0xc9, 0x10, 0xe6, 0x4e, 0x87, 0xfb, 0xf3, 0x02, 0x21,
    0x4e, 0xdb, 0xe3, 0xf2};

static const uint8_t hmac_sha512_in[128] = {
    0xac, 0x93, 0x96, 0x59, 0xdc, 0x5f, 0x66, 0x8c, 0x99, 0x69, 0xc0, 0x53,
    0x04, 0x22, 0xe3, 0x41, 0x7a, 0x46, 0x2c, 0x8b, 0x66, 0x5e, 0x8d, 0xb2,
    0x5a, 0x88, 0x3a, 0x62, 0x5f, 0x7a, 0xa5, 0x9b, 0x89, 0xc5, 0xad, 0x0e,
    0xce, 0x57, 0x12, 0xca, 0x17, 0x44, 0x2d, 0x17, 0x98, 0xc6, 0xde, 0xa2,
    0x5d, 0x82, 0xc5, 0xdb, 0x26, 0x0c, 0xb5, 0x9c, 0x75, 0xae, 0x65, 0x0b,
    0xe5, 0x65, 0x69, 0xc1, 0xbd, 0x2d, 0x61, 0x2c, 0xc5, 0x7e, 0x71, 0x31,
    0x59, 0x17, 0xf1, 0x16, 0xbb, 0xfa, 0x65, 0xa0, 0xae, 0xb8, 0xaf, 0x78,
    0x40, 0xee, 0x83, 0xd3, 0xe7, 0x10, 0x1c, 0x52, 0xcf, 0x65, 0x2d, 0x27,
    0x73, 0x53, 0x1b, 0x7a, 0x6b, 0xdd, 0x69, 0x0b, 0x84, 0x6a, 0x74, 0x18,
    0x16, 0xc8, 0x60, 0x81, 0x92, 0x70, 0x52, 0x2a, 0x5b, 0x0c, 0xdf, 0xa1,
    0xd7, 0x36, 0xc5, 0x01, 0xc5, 0x83, 0xd9, 0x16};

static const uint8_t hmac_sha512_ans[32] = {
    0xbd, 0x3d, 0x2d, 0xf6, 0xf9, 0xd2, 0x84, 0xb4, 0x21, 0xa4, 0x3e,
    0x5f, 0x9c, 0xb9, 0x4b, 0xc4, 0xff, 0x88, 0xa8, 0x82, 0x43, 0xf1,
    0xf0, 0x13, 0x3b, 0xad, 0x0f, 0xb1, 0x79, 0x1f, 0x65, 0x69};

// P256,SHA-256 CAVP vector
// Msg = 44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56
// d = 519b423d715f8b581f4fa8ee59f4771a5b44c8130b4e3eacca54a56dda72b464
// Qx = 1ccbe91c075fc7f4f033bfa248db8fccd3565de94bbfb12f3c59ff46c271bf83
// Qy = ce4014c68811f9a21a1fdb2c0e6113e06db7ca93b7404e78dc7ccd5ca89a4ca9
// k = 94a1bbb14b906a61a280f245f9e93c7f3b4a6247824f5d33b9670787642a68de
// R = f3ac8061b514795b8843e3d6629527ed2afd6b1f6a555a7acabb5e6f79c8c2ac
// S = 8bf77819ca05a6b2786c76262bf7371cef97b218e96f175a3ccdda2acc058903

static const otcrypto_key_config_t kP256Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = 32,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint8_t p256_d[32] = {
    0x64, 0xb4, 0x72, 0xda, 0x6d, 0xa5, 0x54, 0xca, 0xac, 0x3e, 0x4e,
    0x0b, 0x13, 0xc8, 0x44, 0x5b, 0x1a, 0x77, 0xf4, 0x59, 0xee, 0xa8,
    0x4f, 0x1f, 0x58, 0x8b, 0x5f, 0x71, 0x3d, 0x42, 0x9b, 0x51};

static const uint8_t p256_k[32] = {
    0xde, 0x68, 0x2a, 0x64, 0x87, 0x07, 0x67, 0xb9, 0x33, 0x5d, 0x4f,
    0x82, 0x47, 0x62, 0x4a, 0x3b, 0x7f, 0x3c, 0xe9, 0xf9, 0x45, 0xf2,
    0x80, 0xa2, 0x61, 0x6a, 0x90, 0x4b, 0xb1, 0xbb, 0xa1, 0x94};

static const uint8_t p256_Q[64] = {
    // Qx (Reversed)
    0x83, 0xbf, 0x71, 0xc2, 0x46, 0xff, 0x59, 0x3c, 0x2f, 0xb1, 0xbf, 0x4b,
    0xe9, 0x5d, 0x56, 0xd3, 0xcc, 0x8f, 0xdb, 0x48, 0xa2, 0xbf, 0x33, 0xf0,
    0xf4, 0xc7, 0x5f, 0x07, 0x1c, 0xe9, 0xcb, 0x1c,
    // Qy (Reversed)
    0xa9, 0x4c, 0x9a, 0xa8, 0x5c, 0xcd, 0x7c, 0xdc, 0x78, 0x4e, 0x40, 0xb7,
    0x93, 0xca, 0xb7, 0x6d, 0xe0, 0x13, 0x61, 0x0e, 0x2c, 0xdb, 0x1f, 0x1a,
    0xa2, 0xf9, 0x11, 0x88, 0xc6, 0x14, 0x40, 0xce};

static const uint8_t p256_msg_digest[32] = {
    0x44, 0xac, 0xf6, 0xb7, 0xe3, 0x6c, 0x13, 0x42, 0xc2, 0xc5, 0x89,
    0x72, 0x04, 0xfe, 0x09, 0x50, 0x4e, 0x1e, 0x2e, 0xfb, 0x1a, 0x90,
    0x03, 0x77, 0xdb, 0xc4, 0xe7, 0xa6, 0xa1, 0x33, 0xec, 0x56};

static const uint8_t p256_sig[64] = {
    // R (Reversed)
    0xac, 0xc2, 0xc8, 0x79, 0x6f, 0x5e, 0xbb, 0xca, 0x7a, 0x5a, 0x55, 0x6a,
    0x1f, 0x6b, 0xfd, 0x2a, 0xed, 0x27, 0x95, 0x62, 0xd6, 0xe3, 0x43, 0x88,
    0x5b, 0x79, 0x14, 0xb5, 0x61, 0x80, 0xac, 0xf3,
    // S (Reversed)
    0x03, 0x89, 0x05, 0xcc, 0x2a, 0xda, 0xcd, 0x3c, 0x5a, 0x17, 0x6f, 0xe9,
    0x18, 0xb2, 0x97, 0xef, 0x1c, 0x37, 0xf7, 0x2b, 0x26, 0x76, 0x6c, 0x78,
    0xb2, 0xa6, 0x05, 0xca, 0x19, 0x78, 0xf7, 0x8b};

// P-384,SHA-256 CAVP vector
// Msg = bbbd0a5f645d3fda10e288d172b299455f9dff00e0fbc2833e18cd017d7f3ed1
// d =
// c602bc74a34592c311a6569661e0832c84f7207274676cc42a89f058162630184b52f0d99b855a7783c987476d7f9e6b
// Qx =
// 0400193b21f07cd059826e9453d3e96dd145041c97d49ff6b7047f86bb0b0439e909274cb9c282bfab88674c0765bc75
// Qy =
// f70d89c52acbc70468d2c5ae75c76d7f69b76af62dcf95e99eba5dd11adf8f42ec9a425b0c5ec98e2f234a926b82a147
// k =
// c10b5c25c4683d0b7827d0d88697cdc0932496b5299b798c0dd1e7af6cc757ccb30fcd3d36ead4a804877e24f3a32443
// R =
// b11db00cdaf53286d4483f38cd02785948477ed7ebc2ad609054551da0ab0359978c61851788aa2ec3267946d440e878
// S =
// 16007873c5b0604ce68112a8fee973e8e2b6e3319c683a762ff5065a076512d7c98b27e74b7887671048ac027df8cbf2

static const otcrypto_key_config_t kP384Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = 48,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint8_t p384_d[48] = {
    0x6b, 0x9e, 0x7f, 0x6d, 0x47, 0x87, 0xc9, 0x83, 0x77, 0x5a, 0x85, 0x9b,
    0xd9, 0xf0, 0x52, 0x4b, 0x18, 0x30, 0x26, 0x16, 0x58, 0xf0, 0x89, 0x2a,
    0xc4, 0x6c, 0x67, 0x74, 0x72, 0x20, 0xf7, 0x84, 0x2c, 0x83, 0xe0, 0x61,
    0x96, 0x56, 0xa6, 0x11, 0xc3, 0x92, 0x45, 0xa3, 0x74, 0xbc, 0x02, 0xc6};

static const uint8_t p384_k[48] = {
    0x43, 0x24, 0xa3, 0xf3, 0x24, 0x7e, 0x87, 0x04, 0xa8, 0xd4, 0xea, 0x36,
    0x3d, 0xcd, 0x0f, 0xb3, 0xcc, 0x57, 0xc7, 0x6c, 0xaf, 0xe7, 0xd1, 0x0d,
    0x8c, 0x79, 0x9b, 0x29, 0xb5, 0x96, 0x24, 0x93, 0xc0, 0xcd, 0x97, 0x86,
    0xd8, 0xd0, 0x27, 0x78, 0x0b, 0x3d, 0x68, 0xc4, 0x25, 0x5c, 0x0b, 0xc1};

static const uint8_t p384_Q[96] = {
    // Qx (Reversed)
    0x75, 0xbc, 0x65, 0x07, 0x4c, 0x67, 0x88, 0xab, 0xbf, 0x82, 0xc2, 0xb9,
    0x4c, 0x27, 0x09, 0xe9, 0x39, 0x04, 0x0b, 0xbb, 0x86, 0x7f, 0x04, 0xb7,
    0xf6, 0x9f, 0xd4, 0x97, 0x1c, 0x04, 0x45, 0xd1, 0x6d, 0xe9, 0xd3, 0x53,
    0x94, 0x6e, 0x82, 0x59, 0xd0, 0x7c, 0xf0, 0x21, 0x3b, 0x19, 0x00, 0x04,
    // Qy (Reversed)
    0x47, 0xa1, 0x82, 0x6b, 0x92, 0x4a, 0x23, 0x2f, 0x8e, 0xc9, 0x5e, 0x0c,
    0x5b, 0x42, 0x9a, 0xec, 0x42, 0x8f, 0xdf, 0x1a, 0xd1, 0x5d, 0xba, 0x9e,
    0xe9, 0x95, 0xcf, 0x2d, 0xf6, 0x6a, 0xb7, 0x69, 0x7f, 0x6d, 0xc7, 0x75,
    0xae, 0xc5, 0xd2, 0x68, 0x04, 0xc7, 0xcb, 0x2a, 0xc5, 0x89, 0x0d, 0xf7};

static const uint8_t p384_msg_digest[48] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xbb, 0xbd, 0x0a, 0x5f, 0x64, 0x5d, 0x3f, 0xda,
    0x10, 0xe2, 0x88, 0xd1, 0x72, 0xb2, 0x99, 0x45, 0x5f, 0x9d, 0xff, 0x00,
    0xe0, 0xfb, 0xc2, 0x83, 0x3e, 0x18, 0xcd, 0x01, 0x7d, 0x7f, 0x3e, 0xd1};

static const uint8_t p384_sig[96] = {
    // R (Reversed)
    0x78, 0xe8, 0x40, 0xd4, 0x46, 0x79, 0x26, 0xc3, 0x2e, 0xaa, 0x88, 0x17,
    0x85, 0x61, 0x8c, 0x97, 0x59, 0x03, 0xab, 0xa0, 0x1d, 0x55, 0x54, 0x90,
    0x60, 0xad, 0xc2, 0xeb, 0xd7, 0x7e, 0x47, 0x48, 0x59, 0x78, 0x02, 0xcd,
    0x38, 0x3f, 0x48, 0xd4, 0x86, 0x32, 0xf5, 0xda, 0x0c, 0xb0, 0x1d, 0xb1,
    // S (Reversed)
    0xf2, 0xcb, 0xf8, 0x7d, 0x02, 0xac, 0x48, 0x10, 0x67, 0x87, 0x78, 0x4b,
    0xe7, 0x27, 0x8b, 0xc9, 0xd7, 0x12, 0x65, 0x07, 0x5a, 0x06, 0xf5, 0x2f,
    0x76, 0x3a, 0x68, 0x9c, 0x31, 0xe3, 0xb6, 0xe2, 0xe8, 0x73, 0xe9, 0xfe,
    0xa8, 0x12, 0x81, 0xe6, 0x4c, 0x60, 0xb0, 0xc5, 0x73, 0x78, 0x00, 0x16};

// Test vector comes from the rsa_2048_signature_functest
static const uint32_t rsa2048_mod[64] = {
    0x40d984b1, 0x3611356d, 0x9eb2f35c, 0x031a892c, 0x16354662, 0x6a260bad,
    0xb2b807d6, 0xb7de7ccb, 0x278492e0, 0x41adab06, 0x9e60110f, 0x1414eeff,
    0x8b80e14e, 0x5eb5ae79, 0x0d98fa5b, 0x58bece1f, 0xcf6bdca8, 0x82f5611f,
    0x351e3869, 0x075005d6, 0xe813fe23, 0xdd967a37, 0x682d1c41, 0x9fdd2d8c,
    0x21bdd5fc, 0x4fc459c7, 0x508c9293, 0x1f9ac759, 0x55aacb04, 0x58389f05,
    0x0d0b00fb, 0x59bb4141, 0x68f9e0bf, 0xc2f1a546, 0x0a71ad19, 0x9c400301,
    0xa4f8ecb9, 0xcdf39538, 0xaabe9cb0, 0xd9f7b2dc, 0x0e8b292d, 0x8ef6c717,
    0x720e9520, 0xb0c6a23e, 0xda1e92b1, 0x8b6b4800, 0x2f25082b, 0x7f2d6711,
    0x426fc94f, 0x9926ba5a, 0x89bd4d2b, 0x977718d5, 0x5a8406be, 0x87d090f3,
    0x639f9975, 0x5948488b, 0x1d3d9cd7, 0x28c7956b, 0xebb97a3e, 0x1edbf4e2,
    0x105cc797, 0x924ec514, 0x146810df, 0xb1ab4a49,
};

static const uint32_t rsa2048_exp[64] = {
    0x0b19915b, 0xa6a935e6, 0x426b2e10, 0xb4ff0629, 0x7322343b, 0x3f28c8d5,
    0x190757ce, 0x87409d6b, 0xd88e282b, 0x01c13c2a, 0xebb79189, 0x74cbeab9,
    0x93de5d54, 0xae1bc80a, 0x083a75f2, 0xd574d229, 0xeb46696e, 0x7648cfb6,
    0xe7ad1b36, 0xbd0e81b2, 0x19c72703, 0xebea5085, 0xf8c7d152, 0x34dcf84d,
    0xa437187f, 0x41e4f88e, 0xe4e35f9f, 0xcd8bc6f8, 0x7f98e2f2, 0xffdf75ca,
    0x3698226e, 0x903f2a56, 0xbf21a6dc, 0x97cbf653, 0xe9d80cb3, 0x55dc1685,
    0xe0ebae21, 0xc8171e18, 0x8e73d26d, 0xbbdbaac1, 0x886e8007, 0x673c9da4,
    0xe2cb0698, 0xa9f1ba2d, 0xedab4f0a, 0x197e890c, 0x65e7e736, 0x1de28f24,
    0x57cf5137, 0x631ff441, 0x22539942, 0xcee3fd41, 0xd22b5f8a, 0x995dd87a,
    0xcaa6815c, 0x08ca0fd3, 0x8f996093, 0x30b7c446, 0xf69b11f7, 0xa298dd00,
    0xfd4e8120, 0x059df602, 0x25feb268, 0x0f3f749e,
};

static const uint32_t rsa2048_sig[64] = {
    0xab66c6c7, 0x97effc0a, 0x9869cdba, 0x7b6c09fe, 0x2124d28f, 0x793084b3,
    0x4da24b72, 0x4f6c8659, 0x63e3a27b, 0xbbe8d120, 0x8789190f, 0x1722fe46,
    0x25573178, 0x3accbdb3, 0x1eb7ca00, 0xe8eb40aa, 0x1d3b21a8, 0x9997925e,
    0x1793f81d, 0x12728f54, 0x66e40608, 0x4b1057a0, 0xba433eb3, 0x702c73b2,
    0xa9391740, 0xf838710f, 0xf33cf109, 0x595cee1d, 0x07341be9, 0xcfce52b1,
    0x5b48ba7a, 0xf70e5a0e, 0xdbb98c42, 0x85fd6979, 0xcdb760fc, 0xd2e09553,
    0x70bba417, 0x04e52609, 0xc215420e, 0x2407242e, 0x4f19674b, 0x5d996a9d,
    0xf2fb1d05, 0x88e0fc14, 0xe1a38f0c, 0xd111935d, 0xd23bf5b3, 0xdcd7a882,
    0x0f242315, 0xd7247d51, 0xc247d6ec, 0xe2492739, 0x3dfb115c, 0x031aea7a,
    0xcdcb09c0, 0x29318ddb, 0xd0a10dd8, 0x3307018e, 0xe13c5616, 0x98d4db80,
    0x50692a42, 0x41e94a74, 0x0a6f79eb, 0x1c405c66,
};

static const uint32_t rsa2048_digest[8] = {
    0x7a99dab2, 0x7ce06e96, 0x83f0e143, 0x88e57c80,
    0xcaa4c04b, 0xca023bd1, 0x18a172dc, 0x1709b520,
};

static const otcrypto_key_config_t kRsa2048Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeRsaSignPkcs,
    .key_length = kOtcryptoRsa2048PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Test vector comes from the rsa_4096_signature_functest
static uint32_t rsa4096_mod[128] = {
    0x3114efe5, 0x85c4bdcf, 0x02cdc82c, 0xde80fc8b, 0xea50031c, 0x7c4ceeb0,
    0x17488f53, 0xf071b30b, 0xb1d4b69c, 0xa86ad866, 0xd33d1707, 0xa970c3dc,
    0xf22b2197, 0x2ab3eb21, 0xf9699bf2, 0x4f473ba5, 0xef92361d, 0xcf348dfb,
    0x8dfeae93, 0xc7b2b40c, 0x4ab8c5fc, 0x964c7c04, 0x74fe316c, 0x3a9c60c4,
    0xdea0d12f, 0xff3fed73, 0xf9ae495a, 0xcaacc7d0, 0x19567c96, 0xebead54f,
    0x8ad109a2, 0xa272f676, 0x6398b8b1, 0x3cdee7b2, 0x065717ba, 0x43a405d3,
    0xd476a753, 0x5428afc5, 0x69c52607, 0x0b87bef1, 0x95e0d71a, 0xf63d8d44,
    0xcc710705, 0x43957974, 0x04c40c5f, 0xb02f8766, 0x0d87195e, 0x4a690b24,
    0x21712525, 0xbf4a036b, 0xef593e46, 0x69f8e760, 0x1f538ee5, 0x456b541d,
    0x9d589400, 0x59c05b94, 0x5b26d7fb, 0xb9543c03, 0x78fc971e, 0xd214c970,
    0x87bf02a1, 0xf405ca03, 0x678acef1, 0x9ead0010, 0x92da7874, 0x68ae9ea5,
    0x5d772fa1, 0xae584a1c, 0xa341b921, 0xf9795da6, 0x84137166, 0xd94c6f9a,
    0xe9366e3f, 0xf7b2fe46, 0x371e6534, 0x9a16aa5e, 0x741a0a13, 0xcf2c938d,
    0x164bdfe9, 0xf41e8e1a, 0x76b81c66, 0xfb970138, 0xe4605201, 0x6c4bc2bc,
    0x48ba51ca, 0x910a8698, 0x52b6aeb4, 0x301ba271, 0x7d4b42e4, 0x9a20f366,
    0x456d1b34, 0x2ac2bfcf, 0xa9db50ec, 0x5e2494c3, 0xda83238c, 0x0733ddac,
    0xc11a4611, 0xe6f54599, 0xa080a8de, 0xa83522b7, 0x28f41846, 0xc5c7c09e,
    0xdf176908, 0x2797e007, 0x78c11056, 0xe616c668, 0xf7d34763, 0x94274031,
    0x81890d97, 0xb7975de6, 0xcaa24b43, 0xee537161, 0x5096eb55, 0xc93741ae,
    0xf3b55b92, 0xa911acb9, 0xca9ec1c8, 0x8711d18b, 0xbdff524f, 0x149f474a,
    0xca455764, 0xf5cff3d6, 0x74a00192, 0xbb56c41e, 0xb7b12778, 0xc52ceccb,
    0xb8100867, 0x923d26b1,
};

static uint32_t rsa4096_exp[128] = {
    0x2605e651, 0x2109108d, 0x4c0f18d0, 0xed4cacbe, 0x6b11c61d, 0xbdbc9c78,
    0x2fcbfb38, 0xe077dea9, 0x4a977ff1, 0x90a218e0, 0x010cc1af, 0xed1cf5db,
    0x0a86efb9, 0xf0f0ec3a, 0xdb656795, 0xa6bca8d4, 0x1fc075d6, 0xccb95bca,
    0x1707763e, 0xdb82a4c1, 0x9255f7ad, 0x252a9da3, 0xf3c16658, 0x248f7d36,
    0xcf40085e, 0x01204058, 0xea48ce78, 0x9d1bf875, 0xa40c8a12, 0x4eb8bd8a,
    0xe62df4f6, 0xf29cbee4, 0xe3a10c0e, 0x6a6ed6f1, 0xbd010750, 0xf87aa3cc,
    0x1aa75fe8, 0xfb339c32, 0x7af1eeb7, 0x9e895046, 0xff0f46e5, 0xeeb31968,
    0x3130ab1b, 0xeda00eb9, 0x7955470f, 0xcda8258a, 0x3409f25c, 0x087d75f5,
    0xe9371f6d, 0x73fb2898, 0x1b146fdb, 0x9c7269f6, 0xbc4e0726, 0x3a019ce8,
    0x63a211a9, 0x53d53ac4, 0x56bc03a5, 0x7a62418a, 0x008462ec, 0x08edc6ec,
    0x9ea004b7, 0x297fec02, 0x658a898c, 0x17fecf98, 0xbbdf8614, 0x35d62e48,
    0x732733f0, 0xfab68add, 0xd5f33769, 0x20c3e544, 0x6fb994e6, 0xd6e33454,
    0xe5f47481, 0xd71feec2, 0xfa652698, 0x3f799a71, 0x7c3a04ca, 0x30486fe6,
    0x431e12a1, 0x2c603f8b, 0x5a7d0299, 0x99f6bd53, 0x524c38a0, 0x8282029e,
    0xca2f0fa3, 0xaadc68d6, 0x7ceeccf7, 0xe138bc78, 0x5013f95b, 0x1ac64d4a,
    0xb1280f06, 0x08c35154, 0x145b46d7, 0xcbde4a51, 0x9870bb78, 0x47a61a12,
    0xdd537df8, 0xd4333901, 0x13a2f960, 0xe4d19cb4, 0xc1d4e3fc, 0x787050b5,
    0x16a63e7c, 0x145c7309, 0x1611b6cb, 0x5739689e, 0x87d2a8bd, 0xfd442d5f,
    0x5f977d4f, 0x6b291165, 0xb5fee9cc, 0x450616c8, 0x1ede7a54, 0x4f45584d,
    0x22ab1275, 0x0d47a9a4, 0xd732a9ab, 0xeb225cbf, 0xd043c3bf, 0xd673c558,
    0x71829dad, 0x5bc721d2, 0x66375e47, 0x63a53d3b, 0x16d9ec66, 0x18a2c3b6,
    0x965d9408, 0x19aacb83,
};

static const uint32_t rsa4096_sig[128] = {
    0x431579e6, 0x4a4dc3fd, 0xdd82ee92, 0xee94982b, 0xc005f7e2, 0x85e5b717,
    0x60c59ff2, 0x201ddff2, 0x96f581be, 0x503fe3aa, 0xef0f8180, 0xb47ff82c,
    0xc8a823f8, 0x71738ca0, 0xb83dcf25, 0x17b990c7, 0xd9f1d7fa, 0x80d3ba14,
    0x13ff422f, 0x9d6e56de, 0xb62b47e0, 0xa4f0b9bc, 0x940a9c71, 0x69b2071c,
    0xdbe34edb, 0xfe63d932, 0xccd9c16f, 0x5ef4ed25, 0x1ec79846, 0x07211158,
    0x8cae2c9d, 0x62e2ef5a, 0x252cc4e0, 0xe8baadda, 0xae429633, 0x429f0843,
    0x40dd6200, 0x04c836b0, 0x8c409adf, 0x73b2add1, 0x36aa0a74, 0xfadaef9b,
    0xacee1f74, 0x5b7b180f, 0x8fad3140, 0xcec646a2, 0x408ddf5c, 0x1d38ee7f,
    0xf240d459, 0xfadfc25c, 0x97647ee4, 0x42d965d5, 0xdbf6ee16, 0xc479cf35,
    0x87e33cd3, 0xac88bfce, 0x6f32526e, 0xea801ce0, 0x74feee71, 0x00a6c464,
    0x8eb97ada, 0xb8b03e2e, 0x2743d233, 0x4b013bca, 0x9fe1a670, 0x20a987c8,
    0x0ee01ece, 0xadd617cc, 0xa3fa54ef, 0x52097d80, 0x0a9563a2, 0xb9dbfd84,
    0xf09435ce, 0x98eb3ae0, 0x51bfae20, 0x6a8b4d79, 0x4734e7d8, 0x0ec9625c,
    0x966491e2, 0xb93d5f9d, 0x1ed39811, 0x817e1eff, 0x509fa18f, 0x7662c2f9,
    0x6bc87f86, 0x75790027, 0xa75af1ad, 0x3f7b359e, 0x0e8b0f7a, 0x2812be5d,
    0xcf22b0bf, 0xe8b8a9a1, 0xa4d1270b, 0x990f2b58, 0xd604d2fa, 0x0c0150dd,
    0x98573b4b, 0x26e911fe, 0xc3c16e49, 0x6e32d3b3, 0x74190631, 0x464c406b,
    0x8124ce62, 0x446c3ec5, 0xde5a2c08, 0xd0cf9f9b, 0x1b5b66ca, 0x6e59e9fa,
    0x9b96724a, 0x8ca5eee1, 0xe9a31ba6, 0xd7820685, 0x77f97af5, 0x3f0bb945,
    0xbae35f12, 0xd2cf54e8, 0xe0b58909, 0xa2ae9943, 0x1eb03456, 0x5dcac40b,
    0x05bf5fa0, 0xc745d2c2, 0x624004fb, 0x445c1918, 0x3853399d, 0x738f2ae2,
    0xd31ca0a5, 0x2daf5e53,
};

static const uint32_t rsa4096_digest[16] = {
    0xb893ca9d, 0xf40ba12b, 0x09e4aa43, 0x8c33b554, 0xeec01007, 0x64192c43,
    0xf0513d70, 0x7bc41f0e, 0x46196723, 0x94549bc2, 0xc35e1539, 0x371599ad,
    0x5203c922, 0x43577df0, 0xbd4c7513, 0x43267c48,
};

static const otcrypto_key_config_t kRsa4096Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeRsaSignPkcs,
    .key_length = kOtcryptoRsa4096PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// NIST CAVP vector
// Count = 0
// Key = 5fe01c4baf01cbe07796d5aaef6ec1f45193a98a223594ae4f0ef4952e82e330
// IV = bd587321566c7f1a5dd8652d
// PT =
// 881dc6c7a5d4509f3c4bd2daab08f165ddc204489aa8134562a4eac3d0bcad7965847b102733bb63d1e5c598ece0c3e5dadddd
// AAD = 9013617817dda947e135ee6dd3653382
// CT =
// 16e375b4973b339d3f746c1c5a568bc7526e909ddff1e19c95c94a6ccff210c9a4a40679de5760c396ac0e2ceb1234f9f5fe26
// Tag = abd3d26d65a6275f7a4f56b422acab49
static const uint8_t aes_gcm_256_key[] = {
    0x5f, 0xe0, 0x1c, 0x4b, 0xaf, 0x01, 0xcb, 0xe0, 0x77, 0x96, 0xd5,
    0xaa, 0xef, 0x6e, 0xc1, 0xf4, 0x51, 0x93, 0xa9, 0x8a, 0x22, 0x35,
    0x94, 0xae, 0x4f, 0x0e, 0xf4, 0x95, 0x2e, 0x82, 0xe3, 0x30};

static const uint8_t aes_gcm_256_iv[] = {0xbd, 0x58, 0x73, 0x21, 0x56, 0x6c,
                                         0x7f, 0x1a, 0x5d, 0xd8, 0x65, 0x2d};

static const uint8_t aes_gcm_256_aad[] = {0x90, 0x13, 0x61, 0x78, 0x17, 0xdd,
                                          0xa9, 0x47, 0xe1, 0x35, 0xee, 0x6d,
                                          0xd3, 0x65, 0x33, 0x82};

static const uint8_t aes_gcm_256_pt[] = {
    0x88, 0x1d, 0xc6, 0xc7, 0xa5, 0xd4, 0x50, 0x9f, 0x3c, 0x4b, 0xd2,
    0xda, 0xab, 0x08, 0xf1, 0x65, 0xdd, 0xc2, 0x04, 0x48, 0x9a, 0xa8,
    0x13, 0x45, 0x62, 0xa4, 0xea, 0xc3, 0xd0, 0xbc, 0xad, 0x79, 0x65,
    0x84, 0x7b, 0x10, 0x27, 0x33, 0xbb, 0x63, 0xd1, 0xe5, 0xc5, 0x98,
    0xec, 0xe0, 0xc3, 0xe5, 0xda, 0xdd, 0xdd};

static const uint8_t aes_gcm_256_ct[] = {
    0x16, 0xe3, 0x75, 0xb4, 0x97, 0x3b, 0x33, 0x9d, 0x3f, 0x74, 0x6c,
    0x1c, 0x5a, 0x56, 0x8b, 0xc7, 0x52, 0x6e, 0x90, 0x9d, 0xdf, 0xf1,
    0xe1, 0x9c, 0x95, 0xc9, 0x4a, 0x6c, 0xcf, 0xf2, 0x10, 0xc9, 0xa4,
    0xa4, 0x06, 0x79, 0xde, 0x57, 0x60, 0xc3, 0x96, 0xac, 0x0e, 0x2c,
    0xeb, 0x12, 0x34, 0xf9, 0xf5, 0xfe, 0x26};

static const uint8_t aes_gcm_256_tag[] = {0xab, 0xd3, 0xd2, 0x6d, 0x65, 0xa6,
                                          0x27, 0x5f, 0x7a, 0x4f, 0x56, 0xb4,
                                          0x22, 0xac, 0xab, 0x49};

static const otcrypto_key_config_t kAesGcm256Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesGcm,
    .key_length = 32,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// ACVP vector /acvp/v1/testSessions/665366/vectorSets/3483386 tcId = 21
static const uint8_t aes_256_key[32] = {0};

static const uint8_t aes_256_pt[] = {0x91, 0xfb, 0xef, 0x2d, 0x15, 0xa9,
                                     0x78, 0x16, 0x06, 0x0b, 0xee, 0x1f,
                                     0xea, 0xa4, 0x9a, 0xfe};

static const uint8_t aes_256_ct[] = {0x1b, 0xc7, 0x04, 0xf1, 0xbc, 0xe1,
                                     0x35, 0xce, 0xb8, 0x10, 0x34, 0x1b,
                                     0x21, 0x6d, 0x7a, 0xbe};

static const otcrypto_key_config_t kAes256Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesEcb,
    .key_length = 32,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// SHAKE256 CAVP vector
// Len = 8
// Msg = 0f
// Output = aabb07488ff9edd05d6a603b7791b60a16d45093608f1badc0c9cc9a9154f215

static const uint8_t shake256_in[] = {0x0f};

static const uint8_t shake256_ans[] = {
    0xaa, 0xbb, 0x07, 0x48, 0x8f, 0xf9, 0xed, 0xd0, 0x5d, 0x6a, 0x60,
    0x3b, 0x77, 0x91, 0xb6, 0x0a, 0x16, 0xd4, 0x50, 0x93, 0x60, 0x8f,
    0x1b, 0xad, 0xc0, 0xc9, 0xcc, 0x9a, 0x91, 0x54, 0xf2, 0x15};

// KMAC256 CAVP vector
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
// Sample #4
// Security Strength: 256-bits
// Length of Key is 256-bits
// Key is
// 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F
// 50 51 52 53 54 55 56 57 58 59 5A 5B 5C 5D 5E 5F
// Length of data is 32-bits
// Data is
// 00 01 02 03
// Requested output length is 512-bits
// S (as a character string) is
// "My Tagged Application"

static const otcrypto_key_config_t kKmac256Config = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeKmac256,
    .key_length = 32,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint8_t kmac_256_key_bytes[] = {
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a,
    0x4b, 0x4c, 0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,
    0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f};

static const uint8_t kmac_256_in[] = {0x00, 0x01, 0x02, 0x03};

static const char kmac_256_custom[] = "My Tagged Application";

static const uint8_t kmac_256_ans[] = {
    0x20, 0xC5, 0x70, 0xC3, 0x13, 0x46, 0xF7, 0x03, 0xC9, 0xAC, 0x36,
    0xC6, 0x1C, 0x03, 0xCB, 0x64, 0xC3, 0x97, 0x0D, 0x0C, 0xFC, 0x78,
    0x7E, 0x9B, 0x79, 0x59, 0x9D, 0x27, 0x3A, 0x68, 0xD2, 0xF7, 0xF6,
    0x9D, 0x4C, 0xC3, 0xDE, 0x9D, 0x10, 0x4A, 0x35, 0x16, 0x89, 0xF2,
    0x7C, 0xF6, 0xF5, 0x95, 0x1F, 0x01, 0x03, 0xF3, 0x3F, 0x4F, 0x24,
    0x87, 0x10, 0x24, 0xD9, 0xC2, 0x77, 0x73, 0xA8, 0xDD};

// The functions to run the kats
static status_t kat_sha256_hash(void) {
  otcrypto_sha2_context_t ctx;
  TRY(otcrypto_sha2_init(kOtcryptoHashModeSha256, &ctx));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, sha256_in, sizeof(sha256_in));
  TRY(otcrypto_sha2_update(&ctx, &msg_buf));

  uint32_t act_digest[256 / 32];
  otcrypto_hash_digest_t digest_buf = {
      .data = act_digest,
      .len = 256 / 32,
  };
  TRY(otcrypto_sha2_final(&ctx, &digest_buf));

  if (memcmp(act_digest, sha256_ans, 256 / 8)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_sha512_hash(void) {
  otcrypto_sha2_context_t ctx;
  TRY(otcrypto_sha2_init(kOtcryptoHashModeSha512, &ctx));

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, sha512_in, sizeof(sha512_in));
  TRY(otcrypto_sha2_update(&ctx, &msg_buf));

  uint32_t act_digest[512 / 32];
  otcrypto_hash_digest_t digest_buf = {
      .data = act_digest,
      .len = 512 / 32,
  };
  TRY(otcrypto_sha2_final(&ctx, &digest_buf));

  if (memcmp(act_digest, sha512_ans, 512 / 8)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_sha256_hmac(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, hmac_sha256_in, sizeof(hmac_sha256_in));

  uint32_t keyblob[keyblob_num_words(kSha256Config)];
  TRY(keyblob_from_key_and_mask((uint32_t *)hmac_sha256_key, kTestMask,
                                kSha256Config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = kSha256Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[128 / 32];
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, 128 / 32);

  TRY(otcrypto_hmac(&blinded_key, &msg_buf, &tag_buf));

  if (memcmp(act_tag, hmac_sha256_ans, 128 / 8)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_sha512_hmac(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, hmac_sha512_in, sizeof(hmac_sha512_in));

  uint32_t keyblob[keyblob_num_words(kSha512Config)];
  TRY(keyblob_from_key_and_mask((uint32_t *)hmac_sha512_key, kTestMask,
                                kSha512Config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = kSha512Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  uint32_t act_tag[32 / 4];
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, 32 / 4);

  TRY(otcrypto_hmac(&blinded_key, &msg_buf, &tag_buf));

  if (memcmp(act_tag, hmac_sha512_ans, 32)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_drbg(void) {
  status_t status = entropy_csrng_kat();
  TRY(otcrypto_entropy_init());
  return status;
}

static status_t kat_p256_sign(void) {
  uint32_t keyblob_sk[20] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, p256_d, 32);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t keyblob_scalar[20] = {0};
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
      .checksum = 0,
  };
  memcpy(keyblob_scalar, p256_k, 32);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)p256_msg_digest,
                                   .len = 8};
  uint32_t sig[16];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, 16);

  TRY(otcrypto_ecdsa_p256_sign_config_k(&private_key, &secret_scalar, digest,
                                        &sig_buf));

  if (memcmp(sig, p256_sig, 64)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_p256_base_point_mul(void) {
  uint32_t keyblob_sk[20] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  memcpy(keyblob_sk, p256_d, 32);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t pk_act[16] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_act),
      .key = pk_act,
  };

  TRY(otcrypto_p256_base_point_mult(&private_key, &public_key));

  if (memcmp(pk_act, p256_Q, 64)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_p256_verify(void) {
  hardened_bool_t result;

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(p256_Q),
      .key = (uint32_t *)p256_Q,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)p256_msg_digest,
                                   .len = 8};

  uint32_t sig_data[16] = {0};
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_data, 16);
  memcpy(sig_data, p256_sig, 64);

  TRY(otcrypto_ecdsa_p256_verify(&public_key, digest, &sig_buf, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  sig_data[15] ^= 0x1;
  TRY(otcrypto_ecdsa_p256_verify(&public_key, digest, &sig_buf, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolFalse);

  return OTCRYPTO_OK;
}

static status_t kat_p256_point_on_curve(void) {
  hardened_bool_t result;

  otcrypto_unblinded_key_t point = {.key_mode = kOtcryptoKeyModeEcdsaP256,
                                    .key = (uint32_t *)p256_Q,
                                    .key_length = sizeof(p256_Q)};
  point.checksum = integrity_unblinded_checksum(&point);

  TRY(otcrypto_p256_point_on_curve(&point, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  uint32_t bad_point_data[16] = {0};
  memcpy(bad_point_data, p256_Q, 32);
  bad_point_data[0] ^= 0x1;

  otcrypto_unblinded_key_t bad_point = {.key_mode = kOtcryptoKeyModeEcdsaP256,
                                        .key = bad_point_data,
                                        .key_length = sizeof(bad_point_data)};
  bad_point.checksum = integrity_unblinded_checksum(&bad_point);

  TRY(otcrypto_p256_point_on_curve(&bad_point, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolFalse);

  return OTCRYPTO_OK;
}

static status_t kat_p384_sign(void) {
  uint32_t keyblob_sk[28] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };

  memcpy(keyblob_sk, p384_d, 48);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t keyblob_scalar[28] = {0};
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
      .checksum = 0,
  };
  memcpy(keyblob_scalar, p384_k, 48);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)p384_msg_digest,
                                   .len = 12};
  uint32_t sig[24];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, 24);

  TRY(otcrypto_ecdsa_p384_sign_config_k(&private_key, &secret_scalar, digest,
                                        &sig_buf));

  if (memcmp(sig, p384_sig, 96)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_p384_base_point_mul(void) {
  uint32_t keyblob_sk[28] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, p384_d, 48);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t pk_act[24] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk_act),
      .key = pk_act,
  };

  TRY(otcrypto_p384_base_point_mult(&private_key, &public_key));

  if (memcmp(pk_act, p384_Q, 96)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_p384_verify(void) {
  hardened_bool_t result;

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_Q),
      .key = (uint32_t *)p384_Q,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)p384_msg_digest,
                                   .len = 12};

  uint32_t sig_data[24] = {0};
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_data, 24);
  memcpy(sig_data, p384_sig, 96);

  TRY(otcrypto_ecdsa_p384_verify(&public_key, digest, &sig_buf, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  sig_data[23] ^= 0x1;
  TRY(otcrypto_ecdsa_p384_verify(&public_key, digest, &sig_buf, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolFalse);

  return OTCRYPTO_OK;
}

static status_t kat_p384_point_on_curve(void) {
  hardened_bool_t result;

  otcrypto_unblinded_key_t point = {.key_mode = kOtcryptoKeyModeEcdsaP384,
                                    .key = (uint32_t *)p384_Q,
                                    .key_length = sizeof(p384_Q)};
  point.checksum = integrity_unblinded_checksum(&point);

  TRY(otcrypto_p384_point_on_curve(&point, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  uint32_t bad_point_data[24] = {0};
  memcpy(bad_point_data, p384_Q, 48);
  bad_point_data[0] ^= 0x1;

  otcrypto_unblinded_key_t bad_point = {.key_mode = kOtcryptoKeyModeEcdsaP384,
                                        .key = bad_point_data,
                                        .key_length = sizeof(bad_point_data)};
  bad_point.checksum = integrity_unblinded_checksum(&bad_point);

  TRY(otcrypto_p384_point_on_curve(&bad_point, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolFalse);

  return OTCRYPTO_OK;
}

static status_t kat_rsa2048_verify(void) {
  otcrypto_const_word32_buf_t modulus_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa2048_mod, 64);

  uint32_t public_key_data[64];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = public_key_data,
  };

  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus_buf,
                                        &public_key));

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)rsa2048_digest,
                                   .len = 8,
                                   .mode = kOtcryptoHashModeSha256};
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa2048_sig, 64);

  hardened_bool_t result = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, digest, kOtcryptoRsaPaddingPkcs,
                          &sig_buf, &result));

  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

static status_t kat_rsa4096_sign(void) {
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa4096_exp, 128);
  uint32_t zero_share[128] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, zero_share, 128);
  otcrypto_const_word32_buf_t modulus =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa4096_mod, 128);

  uint32_t keyblob[kOtcryptoRsa4096PrivateKeyblobBytes / 4];
  otcrypto_blinded_key_t private_key = {
      .config = kRsa4096Config,
      .keyblob = keyblob,
      .keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes,
  };

  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize4096, &modulus, &d_share0, &d_share1, &private_key));

  otcrypto_hash_digest_t digest_struct = {.data = (uint32_t *)rsa4096_digest,
                                          .len = 16,
                                          .mode = kOtcryptoHashModeSha512};
  uint32_t act_sig[128];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_sig, 128);

  TRY(otcrypto_rsa_sign(&private_key, digest_struct, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));

  if (memcmp(act_sig, rsa4096_sig, 512)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_rsa4096_verify(void) {
  otcrypto_const_word32_buf_t modulus_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa4096_mod, 128);
  uint32_t public_key_data[kOtcryptoRsa4096PublicKeyBytes / 4];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
      .key = public_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096, &modulus_buf,
                                        &public_key));

  otcrypto_hash_digest_t digest = {.data = (uint32_t *)rsa4096_digest,
                                   .len = 16,
                                   .mode = kOtcryptoHashModeSha512};
  otcrypto_const_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, rsa4096_sig, 128);

  hardened_bool_t result;
  TRY(otcrypto_rsa_verify(&public_key, digest, kOtcryptoRsaPaddingPkcs,
                          &sig_buf, &result));
  HARDENED_CHECK_EQ(result, kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

static status_t kat_aes_gcm_256_encrypt(void) {
  uint32_t keyblob[keyblob_num_words(kAesGcm256Config)];
  TRY(keyblob_from_key_and_mask((uint32_t *)aes_gcm_256_key, kTestMask,
                                kAesGcm256Config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kAesGcm256Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  key.checksum = integrity_blinded_checksum(&key);

  otcrypto_const_byte_buf_t pt_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, aes_gcm_256_pt, sizeof(aes_gcm_256_pt));
  otcrypto_const_byte_buf_t aad_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, aes_gcm_256_aad, sizeof(aes_gcm_256_aad));
  otcrypto_const_word32_buf_t iv_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, (uint32_t *)aes_gcm_256_iv, 3);

  uint8_t ct_act[51];
  otcrypto_byte_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, ct_act, 51);

  uint32_t tag_act[4];
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tag_act, 4);

  TRY(otcrypto_aes_gcm_encrypt(&key, &pt_buf, &iv_buf, &aad_buf,
                               kOtcryptoAesGcmTagLen128, &ct_buf, &tag_buf));

  if (memcmp(ct_act, aes_gcm_256_ct, sizeof(aes_gcm_256_ct))) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (memcmp(tag_act, aes_gcm_256_tag, sizeof(aes_gcm_256_tag))) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_aes_ecb_256_decrypt(void) {
  uint32_t keyblob[keyblob_num_words(kAes256Config)];
  TRY(keyblob_from_key_and_mask((uint32_t *)aes_256_key, kTestMask,
                                kAes256Config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = kAes256Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  key.checksum = integrity_blinded_checksum(&key);

  otcrypto_const_byte_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (uint8_t *)aes_256_ct, 16);

  uint32_t pt_act[12] = {0};
  otcrypto_byte_buf_t pt_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, (uint8_t *)pt_act, 16);

  TRY(otcrypto_aes(&key, NULL, kOtcryptoAesModeEcb,
                   kOtcryptoAesOperationDecrypt, &ct_buf,
                   kOtcryptoAesPaddingNull, &pt_buf));

  if (memcmp(pt_act, aes_256_pt, 16)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_shake_256(void) {
  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, shake256_in, sizeof(shake256_in));

  uint32_t act_digest[256 / 32];
  otcrypto_hash_digest_t digest_buf = {
      .data = act_digest,
      .len = 256 / 32,
  };
  TRY(otcrypto_shake256(&msg_buf, &digest_buf));

  if (memcmp(act_digest, shake256_ans, 256 / 8)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

static status_t kat_kmac_256(void) {
  uint32_t keyblob[keyblob_num_words(kKmac256Config)];
  TRY(keyblob_from_key_and_mask((uint32_t *)kmac_256_key_bytes, kTestMask,
                                kKmac256Config, keyblob));

  otcrypto_blinded_key_t blinded_key = {
      .config = kKmac256Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = integrity_blinded_checksum(&blinded_key);

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kmac_256_in, sizeof(kmac_256_in));

  otcrypto_const_byte_buf_t custom_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)kmac_256_custom,
      sizeof(kmac_256_custom) - 1);

  uint32_t act_tag[16] = {0};
  otcrypto_word32_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, act_tag, 16);

  TRY(otcrypto_kmac(&blinded_key, &msg_buf, &custom_buf, 64, &tag_buf));

  if (memcmp(act_tag, kmac_256_ans, 64)) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

// A function pointer type for KAT functions.
typedef status_t (*kat_func_t)(void);

// A struct to hold a test ID and its corresponding KAT function.
typedef struct kat_dispatch {
  const uint64_t test_id;
  const kat_func_t func;
} kat_dispatch_t;

// The dispatch table for all KATs.
static const kat_dispatch_t kKatDispatch[] = {
    {OTCRYPTO_KAT_HASH_SHA256, &kat_sha256_hash},
    {OTCRYPTO_KAT_HASH_SHA512, &kat_sha512_hash},
    {OTCRYPTO_KAT_HMAC_SHA256, &kat_sha256_hmac},
    {OTCRYPTO_KAT_HMAC_SHA512, &kat_sha512_hmac},
    {OTCRYPTO_KAT_DRBG, &kat_drbg},
    {OTCRYPTO_KAT_P256_SIGN, &kat_p256_sign},
    {OTCRYPTO_KAT_P256_VERIFY, &kat_p256_verify},
    {OTCRYPTO_KAT_P256_BASE_POINT_MUL, &kat_p256_base_point_mul},
    {OTCRYPTO_KAT_P256_POINT_ON_CURVE, &kat_p256_point_on_curve},
    {OTCRYPTO_KAT_P384_SIGN, &kat_p384_sign},
    {OTCRYPTO_KAT_P384_VERIFY, &kat_p384_verify},
    {OTCRYPTO_KAT_P384_BASE_POINT_MUL, &kat_p384_base_point_mul},
    {OTCRYPTO_KAT_P384_POINT_ON_CURVE, &kat_p384_point_on_curve},
    {OTCRYPTO_KAT_RSA2048_VERIFY, &kat_rsa2048_verify},
    {OTCRYPTO_KAT_RSA4096_VERIFY, &kat_rsa4096_verify},
    {OTCRYPTO_KAT_RSA4096_SIGN, &kat_rsa4096_sign},
    {OTCRYPTO_KAT_AES_GCM_256_ENCRYPT, &kat_aes_gcm_256_encrypt},
    {OTCRYPTO_KAT_AES_ECB_256_DECRYPT, &kat_aes_ecb_256_decrypt},
    {OTCRYPTO_KAT_SHAKE_256, &kat_shake_256},
    {OTCRYPTO_KAT_KMAC_256, &kat_kmac_256},
};

status_t run_kats(otcrypto_kat_id_t tests) {
  if (tests.flags == 0 || tests.flags >= (1 << kTestLastBit)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Run all requested tests.
  for (size_t i = 0; i < kTestLastBit; ++i) {
    if ((tests.flags & kKatDispatch[i].test_id) != 0) {
      TRY(kKatDispatch[i].func());
    }
  }

  return OTCRYPTO_OK;
}
