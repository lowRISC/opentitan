// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`SecurityLevel::STRONGBOX`:
 * `SigningOperationsTest.Rsa*` & `EncryptionOperationsTest.Rsa*`) and Android
 * CTS (`StrongboxRSACipherTest`, `StrongboxRSASignatureTest`, `CipherTest`, and
 * `SignatureTest` with `isStrongbox = true`) conformance test suite for
 * `otcrypto_rsa`.
 *
 * Upstream AOSP References:
 *   - `hardware/interfaces/security/keymint/aidl/vts/functional/`
 *     - `KeyMintTest.cpp` (lines 206, Signing lines 2935-3415; Encryption
 *       lines 5410-5834)
 *   - `cts/tests/tests/keystore/src/android/keystore/cts/`
 *     - `CipherTest.java`, `RSACipherTest.java`, &
 *       `StrongboxRSACipherTest.java`
 *     - `SignatureTest.java`, `RSASignatureTest.java`, &
 *       `StrongboxRSASignatureTest.java`
 *   - `cts/tests/tests/keystore/res/raw/`
 *     - `rsa_key1_pkcs8.der`, `rsa_key2_pkcs8.der`, &
 *       `rsa_key8_2048_pkcs8.der`
 *
 * Test Mapping:
 *   - `rsa_vts_signing_no_digest_and_raw_test`:
 *     - `TEST_P(SigningOperationsTest, RsaSuccess)` (L2935)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestSuccess)` (L3122)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestTooLong)` (L3141)
 *     - `TEST_P(SigningOperationsTest, RsaNoDigest)` (L3321)
 *     - `TEST_P(SigningOperationsTest, RsaSignTooLargeMessage)` (L3399)
 *     - `RSASignatureTest.java:71` (`testMaxMessageSizeWhenNoDigestUsed` with
 *       `rsa_key8_2048_pkcs8.der` and `KeyMintTest.cpp:206` `rsa_2048_key`)
 *   - `rsa_vts_signing_pkcs1_and_pss_hashes_test`:
 *     - `TEST_P(SigningOperationsTest, RsaAllPaddingsAndDigests)` (L2954)
 *     - `TEST_P(SigningOperationsTest, RsaPssSha256Success)` (L3039)
 *     - `TEST_P(SigningOperationsTest, RsaPkcs1Sha256Success)` (L3104)
 *     - `SignatureTest.java:132-230` (`SHORT_MSG_KAT_SIGNATURES` /
 *       `testSmallMsgKat`)
 *     - `SignatureTest.java:288-330, 756` (`LONG_MSG_KAT_SIGNATURES` /
 *       `testLongMsgKat`)
 *   - `rsa_vts_encryption_modes_test`:
 *     - `TEST_P(EncryptionOperationsTest, RsaNoPaddingSuccess)` (L5410)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepInvalidDigest)` (L5525)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepWithMGFDigestSuccess)` (L5591)
 *     - `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (L5801)
 *     - `CipherTest.java:192-211` (`KAT_VECTORS` for `RSA/ECB/NoPadding` and
 *       `RSA/ECB/PKCS1Padding`)
 *     - `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`)
 *     - `CipherTest.java:956` (`testMaxSizedPlaintextSupported`) & `1036`
 *       (`testLargerThanMaxSizedPlaintextRejected`)
 *     - `RSACipherTest.java:71-265` (`StrongboxRSACipherTest` raw RSA boundary
 *       messages `n - 1`, `n`, `n + 1`, and oversized inputs with
 *       `rsa_key8_2048_pkcs8`)
 *   - `rsa_cts_oaep_sha256_mgf1_sha1_kat_test`:
 *     - `CipherTest.java:240-249` (`KAT_VECTORS` for
 *       `RSA/ECB/OAEPWithSHA-256AndMGF1Padding`)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepSuccess)` (L5463)
 *     - `TEST_P(EncryptionOperationsTest, RsaOaepMGFDigestDefaultSuccess)`
 *       (L5662)
 *   - `rsa_cts_pkcs1_v15_empty_plaintext_short_buf_test`:
 *     - `CipherTest.java:398` (`testEmptyPlaintextEncryptsAndDecrypts`)
 *     - `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (L5801)
 *   - `rsa_vts_signing_zero_length_no_digest_test`:
 *     - `TEST_P(SigningOperationsTest, RsaNoDigest)` (L3321, 0-byte message)
 */

enum {
  kRsa2048NumBytes = 2048 / 8,
  kRsa2048NumWords = kRsa2048NumBytes / sizeof(uint32_t),
  kMaxPkcs1v15PayloadBytes = kRsa2048NumBytes - 11,
  kMaxOaepSha256PayloadBytes = kRsa2048NumBytes - 2 * 32 - 2,
};

// Test RSA-2048 key pair (e = 65537).
static const uint32_t kTestModulus[kRsa2048NumWords] = {
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

static const uint32_t kTestPrivateExponent[kRsa2048NumWords] = {
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

static const uint8_t kTestMessage[] = "KeyMint VTS/CTS RSA test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

static const uint8_t kTestLabel[] = "KeyMint OAEP label";
static const size_t kTestLabelLen = sizeof(kTestLabel) - 1;

// Android CTS `R.raw.rsa_key8_2048_pkcs8` (`StrongboxRSASignatureTest.java`,
// `StrongboxRSACipherTest.java`).
static const uint32_t kCtsRsaKey8Modulus[kRsa2048NumWords] = {
    0x2b64e423, 0xebf187c3, 0x5797b207, 0xcc35c8bd, 0x4c76c5c4, 0x486352a9,
    0x76ddc0d6, 0xfac39d0f, 0xf9b58c94, 0xc53f0526, 0x2e582708, 0x38ead867,
    0x4842837b, 0x94f22c37, 0x68a21cf1, 0x6aba54cd, 0xd177d037, 0x03f4b251,
    0xd3091006, 0x7deb6ecd, 0x01f4f39b, 0xa4b194c1, 0x1828c4ec, 0x438c82ca,
    0xeac3ccd0, 0x95420ca8, 0x890fd635, 0x59558ef8, 0xf4192fcf, 0xf7ce788f,
    0x2451b55b, 0xb45965a0, 0x52023de2, 0xb46c662d, 0x2006a615, 0xb5982694,
    0x891a7c65, 0x3dff0da3, 0xeece1213, 0x72a86fd4, 0x900f0738, 0xfc7189a8,
    0x5e90c8a0, 0x60f8b721, 0x7dad5a68, 0xa57a441c, 0x460ccebd, 0x91b202a9,
    0x648bdd7b, 0x2dfe1002, 0x4cd1dd5f, 0x49b124d4, 0x9abcbac2, 0xa86aac99,
    0x8df7da8c, 0x9b1c9280, 0xa6de1465, 0xee01ab9a, 0xc9b8cc19, 0x0b1f41b8,
    0x971c788c, 0x37bde4ee, 0x9edde46a, 0xd3967b53,
};
static const uint32_t kCtsRsaKey8PrivExp[kRsa2048NumWords] = {
    0x9b046e41, 0xaf1a5ff2, 0x7fec4d1a, 0x21a71b37, 0x66d4087f, 0xea104634,
    0xba0715a6, 0x299bbabe, 0x8a9f966f, 0x01c343cd, 0xe6786b11, 0x6b3008c5,
    0xbb7b69e7, 0x873f6be1, 0xb0104788, 0x924349fe, 0xe86fd383, 0x0a3b1973,
    0xa6584c70, 0xa37dff71, 0x18c6465b, 0x988beaf3, 0x40f90ae5, 0xf2c69ee6,
    0x93bb638e, 0xc252cff1, 0x805afc63, 0xab6e496e, 0x6cc04eaa, 0xa576d018,
    0xefe20bb6, 0xea3c16ed, 0x9ebf37eb, 0xf19dc2f2, 0x7632660b, 0x910acd6f,
    0xffa1ded0, 0x8807ec92, 0x17ab035f, 0x641cefac, 0x837ada33, 0x12d5e649,
    0x9acfd730, 0x3c32c851, 0x83dc129b, 0x022b0466, 0x504b5b12, 0x377af032,
    0x16d4bc07, 0x511d1703, 0x2309bf13, 0x3f2015b5, 0x43f00c11, 0xddfac294,
    0x3631b07c, 0x1ec97643, 0x47719bb8, 0x1d7f333e, 0x06457a27, 0x26dc583c,
    0x4f54a0cb, 0x78ee1b77, 0x6310396a, 0xaa951370,
};

// Android KeyMint VTS `rsa_2048_key` (`KeyMintTest.cpp:206`).
static const uint32_t kVtsRsa2048Modulus[kRsa2048NumWords] = {
    0x295070c5, 0x6924cdf7, 0xb220d780, 0xeef8a713, 0xe643b079, 0x9838f29e,
    0x24544b5f, 0x8ea348b5, 0x4286b094, 0x3f62204e, 0x35b3870b, 0x39f33bff,
    0x467b7193, 0xd0cb88f9, 0xd7f6b20d, 0x14227d1b, 0x552aba67, 0xf111a949,
    0x7f190358, 0x3ee22440, 0x9bdb1438, 0x6ffbf319, 0x568e892b, 0x33d29d84,
    0x9d691861, 0xa714c280, 0xa7dd9a81, 0x6cc2da66, 0x9164ccf7, 0x308f2504,
    0x2fcb70ff, 0x5126f096, 0x00670e6c, 0x16dfaa57, 0x5c8b8402, 0xe3bad405,
    0x07128df3, 0x02d07593, 0x1f6ecdeb, 0x7b93b5a8, 0x340dbfa2, 0x8b59ab48,
    0x64bfe7ab, 0x54a2fd46, 0x1f777565, 0x9caf0e62, 0xf8117dc8, 0xe49500ac,
    0x79b97382, 0x7a3ecd9b, 0x9b44510e, 0xee11f631, 0xedec383d, 0xd14911f2,
    0x8dc763d9, 0x91d339f5, 0xd739a617, 0x29e63b2e, 0x76a5a180, 0x897e3184,
    0x7056e80a, 0x299f9a6a, 0x56d443b1, 0xbebc342b,
};
static const uint32_t kVtsRsa2048PrivExp[kRsa2048NumWords] = {
    0x3604db01, 0xb5db10f9, 0x2e901209, 0xf8e3473f, 0xb6cbe7b0, 0x153edc6e,
    0x9130d022, 0xab97f97b, 0xc787fee4, 0x42817809, 0xfc528fe4, 0x20be2a08,
    0x97c71ead, 0x1d5ab053, 0x91a164d0, 0xd604ba80, 0x9228a352, 0x46863b09,
    0xa0fb5b54, 0x04d0a678, 0x7d201497, 0xc42daf73, 0xf5db408e, 0x1b292e9e,
    0x0d91326e, 0xe9958cc3, 0x7a20d350, 0x365fd5ee, 0xfb163124, 0xe4090d06,
    0x5bf074a4, 0x6ab70664, 0x8e68b0ec, 0xd4f6f7d3, 0xe3f3a827, 0xcccafa7d,
    0xe28fdf04, 0x339302cc, 0x2e84c9a4, 0xd59eaeb9, 0x6f93f790, 0x8354133e,
    0xb3c09a7b, 0x2686c7b4, 0x6a735c66, 0x8ce6fd51, 0x4ad9c48a, 0x2ea9ca8f,
    0xbb3d563a, 0x11951377, 0x4be1be39, 0x0fc43083, 0x59fdef1c, 0xbecf1d46,
    0x344abf5f, 0x5ab10030, 0x6dfd1b13, 0x9366ce17, 0x7c7ff35f, 0x38db3dbc,
    0xcd1ca997, 0xf075353c, 0x5f2f584e, 0x69f377f3,
};

// Android CTS `R.raw.rsa_key1_pkcs8` (`SignatureTest.java:132-230, 288-330`).
static const uint32_t kCtsRsaKey1Modulus[kRsa2048NumWords] = {
    0xd92e0d1b, 0xce2f1e85, 0xbb6873fe, 0xba242e6b, 0x063bc171, 0x5588891e,
    0x026b82e3, 0x662b3af7, 0x6861b531, 0x7f32a064, 0xa4f2e40f, 0x525d08a9,
    0x3e1e3f90, 0xf8a04bad, 0x800e2e7e, 0xa6802e08, 0x97335cc0, 0xac1105db,
    0x0748f766, 0x91445f81, 0xd8a1c606, 0x8af766bb, 0xf0e62491, 0xbc94abb2,
    0x822c75b4, 0xd5847d32, 0x865067e2, 0xfc5cf901, 0xe3cf871b, 0x27712a16,
    0x84d28d74, 0x628fc019, 0x95807a5d, 0x4b1e4d00, 0xb381b33c, 0xf8535b34,
    0xfdea7d47, 0x86ae9d71, 0xfb849c8c, 0xed30dfa8, 0xc9d21df3, 0xb722e302,
    0xdb0e2856, 0x7c7e80dd, 0x27e90213, 0x0e06036a, 0xe56195f4, 0xd11996bb,
    0x9813efd4, 0x477a1a7e, 0x792e2bf3, 0xca5c8516, 0x1d028c69, 0xad38e7a3,
    0xd09131f4, 0xecf87648, 0xa42ebb5d, 0xa5288112, 0xdb2d7a82, 0x4b2c7fdf,
    0x05ce7552, 0xcd8f4358, 0x194eb182, 0xa0f855d8,
};
static const uint32_t kCtsRsaKey1PrivExp[kRsa2048NumWords] = {
    0xa6969321, 0xd405ec7b, 0x10214571, 0x0628ad1b, 0x200ca6e4, 0x02be5a90,
    0xdf7ab15a, 0x00028eca, 0x934138b0, 0xabf4d82a, 0x6825c2c3, 0xd060bbed,
    0x8bad093e, 0x50bd2e36, 0x2d92880f, 0x573919cd, 0x069753c9, 0xe5502044,
    0x0975544d, 0x9e7cafd0, 0xeeec95e2, 0x64260aa7, 0x312fb96c, 0xd2740049,
    0xd94b1803, 0x46f5a373, 0x223d2527, 0xf2b82abc, 0x6b51cee6, 0x1cc0713c,
    0x8c24c504, 0x27bcdc78, 0x4e5e6537, 0xcff08bb0, 0x3a2496d4, 0x0a8f00cc,
    0x0e166e91, 0xdfa180e9, 0xf5d61c52, 0x8965e5ee, 0x2340db06, 0x663b8ccc,
    0xad1f2bfc, 0x93291db8, 0x977f004c, 0x6116e1f7, 0x6953eac0, 0x06c41c97,
    0x84f536de, 0xa3edb422, 0x4983a3ec, 0xe3728aab, 0xffca6b7f, 0x6871f63c,
    0x9ff8ffbb, 0x8d64e712, 0x3394c017, 0xdb3619e4, 0xf363de41, 0x2750ca7f,
    0xe7497abc, 0xe93cf82c, 0x643a07e3, 0x9a076765,
};
static const uint32_t kCtsRsaNoneSig[kRsa2048NumWords] = {
    0x78d70eb0, 0x1f5ab6d5, 0xce717263, 0x41fbc17e, 0xa0debccb, 0x3b968635,
    0x98942d23, 0x0c78b4dc, 0x6e70c768, 0x86a00123, 0x3537680c, 0x8728455e,
    0x8867de05, 0x302f0fd2, 0xc95ea69f, 0x4de77831, 0x9252f4f7, 0x68155367,
    0x032add52, 0x53bf45e7, 0x9475f9be, 0x4dd7cbfa, 0x917e78ae, 0x6bc9fb30,
    0x8ecd6042, 0xb8b63eb9, 0xb45e1dd1, 0xc7c77e50, 0x79d66d38, 0x0224d2ee,
    0x417a8963, 0xbdea1dee, 0xe917680b, 0xa34b890c, 0xe1146aa2, 0xb566ca53,
    0xad96d04b, 0x868b3f8c, 0x353192c3, 0x40799cc0, 0xd8437958, 0xc0d8cc4c,
    0x0df3b5d9, 0x91919eff, 0xf913e1c8, 0x304c9b27, 0x7df0d4c5, 0xe9279958,
    0xcd1036d9, 0x08eb05d0, 0xeeab40b9, 0x29e5daf9, 0x16083ac9, 0x39f56ae6,
    0x0e78e00d, 0x580fee34, 0x88015d14, 0x63a53067, 0xa83b5d64, 0x7d7738e6,
    0x6adb2d5a, 0x9a5c4557, 0xe514ead2, 0x257d0704,
};
static const uint8_t kCtsSigMsg[23] = {
    0xec, 0x17, 0x47, 0x29, 0xc4, 0xf5, 0xc5, 0x70, 0xba, 0x0d, 0xe4, 0xc4,
    0x24, 0xcd, 0xcb, 0xf0, 0x36, 0x2a, 0x77, 0x18, 0x03, 0x94, 0x64,
};

// Android CTS `R.raw.rsa_key2_pkcs8` (`CipherTest.java:192-249`).
static const uint32_t kCtsRsaKey2Modulus[kRsa2048NumWords] = {
    0x6d2eb95d, 0xe8f2d3fd, 0x4fbde5fd, 0x3ce6f0d2, 0x7c79ae8f, 0x1b4fcdc4,
    0xabdad957, 0x696d8e92, 0xff22aa71, 0x7ea1b175, 0xb3e5ff3e, 0x0f822e6b,
    0x2c9c6210, 0xeeb5ddc4, 0x13675d62, 0x70729231, 0x92070869, 0x87fef983,
    0x9319f263, 0x6d86a6a6, 0x9dd0c843, 0x72844336, 0x99124a90, 0x5123f029,
    0xddac2a7d, 0xcba94685, 0x7d363e99, 0xef32f2a1, 0x62dfd58b, 0xf0102a09,
    0x246c4e06, 0x8cbe4af2, 0xf243082f, 0x7904912d, 0x0ff549e1, 0x04371322,
    0xcecbb8c5, 0x17ff59a8, 0xd674703d, 0x68646f63, 0x33425dc6, 0xfa16119b,
    0x90b8caa2, 0x9bf3bba5, 0xef0ece3b, 0xa468a834, 0x702c965a, 0xc97ccc90,
    0xb73b4462, 0xb4330506, 0xd4be8f9a, 0x9f7fa586, 0xca828ccd, 0xbcd3fd2f,
    0x393a9dea, 0x3945db5d, 0x3b1485a0, 0x77d2be35, 0x47f873f7, 0xde98a946,
    0xba7980ee, 0xf49a096e, 0xae39a4d0, 0xaba43abc,
};
static const uint32_t kCtsRsaKey2PrivExp[kRsa2048NumWords] = {
    0xed8dd741, 0x7929539f, 0xadadd559, 0x74cd3830, 0x7ecb8017, 0x55f8b23b,
    0x53e332b5, 0xf2d3a20b, 0xb9ecbe08, 0xe485d15a, 0xe1be6370, 0xaf5a0fa8,
    0x7a6b16f2, 0xf203a7dd, 0xc840af6b, 0x82a9e386, 0xc0ef1390, 0x4a502cfd,
    0x750c7232, 0x4bf9fc70, 0x424a2fc8, 0x4e52abe8, 0xe22bafdb, 0x04f11b20,
    0xdeab2fbc, 0x7e6d2386, 0x22af86ef, 0x951431df, 0xb493daed, 0x1fef4a86,
    0xbd151d56, 0xa3bf1869, 0xe408993d, 0x305d09d3, 0x50863953, 0xba1965ae,
    0x24cb346c, 0x1de07e4f, 0x0f2f09df, 0x0cd26c18, 0xbf8bc6a6, 0x355a3675,
    0xf4e67ac8, 0x8e2967a3, 0x176ce734, 0x3bf315a2, 0xaf6e540f, 0x575db662,
    0x61f5e621, 0x10d96b91, 0x722b4194, 0xc144038d, 0x62c73390, 0x4a48462f,
    0x36075a35, 0xb2b85dd2, 0x4298ebde, 0xa0f75624, 0x4781cead, 0x46ad0add,
    0xc3aa214d, 0xab2c680f, 0xf5402364, 0x3576dc8c,
};
static const uint8_t kCtsRsaOaepSha256Pt[63] = {
    0x33, 0x2c, 0x2f, 0x2f, 0xc0, 0x66, 0xfb, 0x29, 0xec, 0x09, 0x28,
    0xa5, 0x2b, 0x51, 0x11, 0xce, 0x69, 0x65, 0x54, 0x6c, 0xe7, 0x39,
    0x27, 0x34, 0x0c, 0x42, 0xd3, 0x3b, 0x56, 0xb6, 0xba, 0x54, 0x7b,
    0x77, 0xac, 0x36, 0x1a, 0xc0, 0xd1, 0x33, 0x16, 0x34, 0x5c, 0xa9,
    0x53, 0x84, 0x00, 0x23, 0xd8, 0x92, 0xfa, 0x4f, 0xf1, 0xaa, 0x32,
    0xcc, 0x66, 0xd5, 0xaa, 0x88, 0xb7, 0x98, 0x67,
};
static const uint32_t kCtsRsaOaepSha256Ct[kRsa2048NumWords] = {
    0xe1862d74, 0x9dd5173e, 0xd4adb150, 0xdd8d517a, 0x09069468, 0x5d11de90,
    0xa8ba573f, 0x7f45e346, 0x845fdc7c, 0xd85ce423, 0x1d100e67, 0x0b1631be,
    0x9c7fb350, 0x4231c6b7, 0x75d5d755, 0x456dd406, 0xa57cfbfa, 0xacd8ddd3,
    0x49ae44d3, 0x27954f0e, 0x4b50a825, 0x271ddb8c, 0x213f3f24, 0x1683d237,
    0xec0d89bb, 0x8f1d62ed, 0xb791c497, 0xa57ead6d, 0x7519df66, 0x7d947ff9,
    0x1da880c2, 0xb029f1e3, 0xc18bbf55, 0x51230c6b, 0xdf1e6ce6, 0x388128b6,
    0xbfc7b86f, 0xbb4fd7f3, 0x48eb86bb, 0x1efe9c55, 0x1e94abc5, 0x903915e0,
    0x022be6a0, 0xb2203799, 0x077afec7, 0xfcf05bb2, 0x55577b34, 0x38c460c7,
    0xee6efbfe, 0xd5883ff8, 0x0a28873f, 0xa8dfe4cb, 0xae84fb40, 0x715a3d95,
    0xd2f33200, 0xaddcd3e5, 0xa57307a9, 0x6d4f0f63, 0x58faf1b2, 0x4c66bc14,
    0x1b1df508, 0xe116d928, 0xc67a34a7, 0x942c0ba1,
};

/**
 * Helper to construct RSA-2048 public and private keys from given modulus and
 * private exponent arrays.
 */
static status_t construct_custom_rsa2048_keypair(
    const uint32_t *mod_words, const uint32_t *d_words,
    otcrypto_key_mode_t key_mode, uint32_t *pub_key_data,
    otcrypto_unblinded_key_t *public_key, uint32_t *priv_keyblob,
    otcrypto_blinded_key_t *private_key) {
  otcrypto_const_word32_buf_t modulus = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, mod_words, kRsa2048NumWords);
  otcrypto_const_word32_buf_t d_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, d_words, kRsa2048NumWords);
  uint32_t share1[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t d_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1, ARRAYSIZE(share1));

  *public_key = (otcrypto_unblinded_key_t){
      .key_mode = key_mode,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_key_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &modulus,
                                        public_key));

  *private_key = (otcrypto_blinded_key_t){
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = key_mode,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob = priv_keyblob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &modulus, &d_share0, &d_share1, private_key));
  return OK_STATUS();
}

/**
 * Helper to construct RSA-2048 public and private keys for a given key mode.
 */
static status_t construct_rsa2048_keypair(otcrypto_key_mode_t key_mode,
                                          uint32_t *pub_key_data,
                                          otcrypto_unblinded_key_t *public_key,
                                          uint32_t *priv_keyblob,
                                          otcrypto_blinded_key_t *private_key) {
  return construct_custom_rsa2048_keypair(kTestModulus, kTestPrivateExponent,
                                          key_mode, pub_key_data, public_key,
                                          priv_keyblob, private_key);
}

/**
 * Source:
 *   - `KeyMintTest.cpp:2935` — `TEST_P(SigningOperationsTest, RsaSuccess)`
 *   - `KeyMintTest.cpp:3122` —
 *     `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestSuccess)`
 *   - `KeyMintTest.cpp:3141` —
 *     `TEST_P(SigningOperationsTest, RsaPkcs1NoDigestTooLong)`
 *   - `KeyMintTest.cpp:3321` — `TEST_P(SigningOperationsTest, RsaNoDigest)`
 *   - `KeyMintTest.cpp:3399` —
 *     `TEST_P(SigningOperationsTest, RsaSignTooLargeMessage)`
 */
static status_t rsa_vts_signing_no_digest_and_raw_test(void) {
  LOG_INFO("Testing SigningOperationsTest.RsaNoDigest (PKCS#1 v1.5 & Raw)");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  // 1. PKCS#1 v1.5 Sign/Verify with `kOtcryptoHashModeNull` (unhashed raw
  // message up to k - 11 = 245 bytes; `otcrypto_hash_digest_t.len` is in bytes
  // when `mode == kOtcryptoHashModeNull`).
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                &public_key, priv_blob, &private_key));

  uint32_t
      raw_digest_words[ceil_div(kMaxPkcs1v15PayloadBytes, sizeof(uint32_t))];
  memset(raw_digest_words, 0, sizeof(raw_digest_words));
  for (size_t i = 0; i < kMaxPkcs1v15PayloadBytes; ++i) {
    ((uint8_t *)raw_digest_words)[i] = (uint8_t)(0x10u + i);
  }
  otcrypto_hash_digest_t null_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = raw_digest_words,
      .len = kMaxPkcs1v15PayloadBytes,
  };

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  TRY(otcrypto_rsa_sign(&private_key, null_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, null_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Tamper with the unhashed message and verify PKCS#1 v1.5 verification fails.
  raw_digest_words[0] ^= 1u;
  TRY(otcrypto_rsa_verify(&public_key, null_digest, kOtcryptoRsaPaddingPkcs,
                          &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolFalse);
  raw_digest_words[0] ^= 1u;

  // PKCS#1 v1.5 with `kOtcryptoHashModeNull` must reject payloads > 245 bytes
  // (e.g., 246 bytes).
  uint32_t too_long_digest_words[ceil_div(kMaxPkcs1v15PayloadBytes + 1,
                                          sizeof(uint32_t))];
  memset(too_long_digest_words, 0, sizeof(too_long_digest_words));
  otcrypto_hash_digest_t too_long_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = too_long_digest_words,
      .len = kMaxPkcs1v15PayloadBytes + 1,
  };
  TRY_CHECK(otcrypto_rsa_sign(&private_key, too_long_digest,
                              kOtcryptoRsaPaddingPkcs, &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 2. Raw RSA (`PaddingMode::NONE` + `Digest::NONE`):
  // Left-padding short messages with leading zero bytes in big-endian integer
  // order corresponds to reversing `kTestMessage` into the least-significant
  // `kTestMessageLen` bytes of the little-endian `raw_block` word array.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaRaw, pub_data, &public_key,
                                priv_blob, &private_key));
  uint32_t raw_block[kRsa2048NumWords] = {0};
  for (size_t i = 0; i < kTestMessageLen; ++i) {
    ((uint8_t *)raw_block)[i] = kTestMessage[kTestMessageLen - 1 - i];
  }
  otcrypto_hash_digest_t raw_block_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = raw_block,
      .len = sizeof(raw_block),
  };
  TRY(otcrypto_rsa_sign(&private_key, raw_block_digest, kOtcryptoRsaPaddingNull,
                        &sig_buf));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, raw_block_digest,
                          kOtcryptoRsaPaddingNull, &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Raw RSA must reject input numerically >= modulus.
  otcrypto_hash_digest_t ge_mod_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = (uint32_t *)kTestModulus,
      .len = sizeof(kTestModulus),
  };
  TRY_CHECK(otcrypto_rsa_sign(&private_key, ge_mod_digest,
                              kOtcryptoRsaPaddingNull, &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // KeyMintTest.cpp:3321 (`SigningOperationsTest.RsaNoDigest`):
  // RSA-PSS (`kOtcryptoRsaPaddingPss`) with `Digest::NONE`
  // (`kOtcryptoHashModeNull`) must fail with `OTCRYPTO_BAD_ARGS`.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPss, pub_data,
                                &public_key, priv_blob, &private_key));
  TRY_CHECK(otcrypto_rsa_sign(&private_key, null_digest, kOtcryptoRsaPaddingPss,
                              &sig_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 3. Android CTS `RSASignatureTest.java:71`
  // (`StrongboxRSASignatureTest.testMaxMessageSizeWhenNoDigestUsed` using
  // `R.raw.rsa_key8_2048_pkcs8`) and KeyMint VTS `KeyMintTest.cpp:206`
  // (`rsa_2048_key`):
  const struct {
    const uint32_t *n;
    const uint32_t *d;
  } kImportedRsaKeys[2] = {
      {kCtsRsaKey8Modulus, kCtsRsaKey8PrivExp},
      {kVtsRsa2048Modulus, kVtsRsa2048PrivExp},
  };
  for (size_t k = 0; k < ARRAYSIZE(kImportedRsaKeys); ++k) {
    TRY(construct_custom_rsa2048_keypair(kImportedRsaKeys[k].n,
                                         kImportedRsaKeys[k].d,
                                         kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                         &public_key, priv_blob, &private_key));
    TRY(otcrypto_rsa_sign(&private_key, null_digest, kOtcryptoRsaPaddingPkcs,
                          &sig_buf));
    verif_ok = kHardenedBoolFalse;
    TRY(otcrypto_rsa_verify(&public_key, null_digest, kOtcryptoRsaPaddingPkcs,
                            &const_sig_buf, &verif_ok));
    TRY_CHECK(verif_ok == kHardenedBoolTrue);
  }

  return OK_STATUS();
}

/**
 * SigningOperationsTest.RsaAllPaddingsAndDigests, RsaPkcs1Sha256Success, &
 * RsaPssSha256Success (`KeyMintTest.cpp:2954-3115`).
 *
 * On StrongBox (`SecurityLevel::STRONGBOX`), `ValidDigests(true, true)` is
 * `{Digest::NONE, Digest::SHA_2_256}` (`KeyMintAidlTestBase.cpp:1641-1645`,
 * `util/TestUtils.java:160-162`). Tests both PKCS#1 v1.5 and PSS with SHA-256,
 * corrupted signature rejection (`++corrupt[64]`), and the Android CTS
 * `SignatureTest.java` RSA-2048 KAT signatures for StrongBox (`SHA256withRSA`,
 * `SHA256withRSA/PSS`, and `NONEwithRSA`).
 */
static status_t rsa_vts_signing_pkcs1_and_pss_hashes_test(void) {
  LOG_INFO(
      "Testing StrongBox SigningOperationsTest.RsaAllPaddingsAndDigests "
      "(PKCS#1 v1.5 & PSS with SHA-256 and CTS KAT signatures)");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  otcrypto_const_byte_buf_t msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);
  uint32_t sha256_words[256 / 32];
  otcrypto_hash_digest_t sha256_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = sha256_words,
      .len = ARRAYSIZE(sha256_words),
  };
  TRY(otcrypto_sha2_256(&msg_buf, &sha256_digest));

  const otcrypto_rsa_padding_t kPaddings[2] = {kOtcryptoRsaPaddingPkcs,
                                               kOtcryptoRsaPaddingPss};
  const otcrypto_key_mode_t kKeyModes[2] = {kOtcryptoKeyModeRsaSignPkcs,
                                            kOtcryptoKeyModeRsaSignPss};

  for (size_t p = 0; p < ARRAYSIZE(kPaddings); ++p) {
    TRY(construct_rsa2048_keypair(kKeyModes[p], pub_data, &public_key,
                                  priv_blob, &private_key));
    uint32_t sig[kRsa2048NumWords];
    otcrypto_word32_buf_t sig_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
    otcrypto_const_word32_buf_t const_sig_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

    TRY(otcrypto_rsa_sign(&private_key, sha256_digest, kPaddings[p], &sig_buf));
    hardened_bool_t verif_ok = kHardenedBoolFalse;
    TRY(otcrypto_rsa_verify(&public_key, sha256_digest, kPaddings[p],
                            &const_sig_buf, &verif_ok));
    TRY_CHECK(verif_ok == kHardenedBoolTrue);

    // KeyMintTest.cpp:2998: Corrupt middle word of signature and verify
    // verification fails (`verif_ok == kHardenedBoolFalse`).
    sig[kRsa2048NumWords / 2] ^= 1u;
    verif_ok = kHardenedBoolTrue;
    TRY(otcrypto_rsa_verify(&public_key, sha256_digest, kPaddings[p],
                            &const_sig_buf, &verif_ok));
    TRY_CHECK(verif_ok == kHardenedBoolFalse);
  }

  // Android CTS `SignatureTest.java:132-230` (`SHORT_MSG_KAT_SIGNATURES` /
  // `testSmallMsgKat`) with
  // `TestUtils.getDigestsForKeyMintImplementation(true)` (`NONE` and
  // `SHA-256`): Verify StrongBox RSA-2048 KAT signatures (`SHA256withRSA`,
  // `SHA256withRSA/PSS`, and `NONEwithRSA`) using `R.raw.rsa_key1_pkcs8` over
  // the 23-byte message `ec174729c4f5c570ba0de4c424cdcbf0362a7718039464`.
  static const uint32_t kCtsRsaPkcs1Sha256Sig[kRsa2048NumWords] = {
      0x9da99745, 0x41fa129c, 0x6bb104ee, 0x55099bdb, 0x2c7b5ec8, 0xae6a67df,
      0x64dc2065, 0x6b472fd7, 0x622919cf, 0x1fee9d2e, 0x91bd6456, 0x0264b27d,
      0xb5309238, 0x68691adf, 0xc2ec999b, 0x00ce3899, 0x69ae6980, 0xfc81636e,
      0x512dbdc4, 0x8e8887ff, 0x1be51e0f, 0xc8a0ee6a, 0xff443948, 0x967fb7ec,
      0xf9664540, 0x4df4225c, 0xe28f4189, 0x7e1de2b8, 0xfc6f70fa, 0x4a29369f,
      0x095987af, 0x865b2d01, 0x36029820, 0x3e76c10d, 0xccc9a9ec, 0xe30a9dd6,
      0xa8e10ca2, 0x053ef0db, 0x536d61c8, 0x028ad906, 0xddef264d, 0xf640b589,
      0x054ad8f4, 0xc9407106, 0xc7c32810, 0x65b578bb, 0xdec5f015, 0x4b01112a,
      0x574df545, 0x1022fcd3, 0x89965045, 0x729ccc23, 0x4e10b1ba, 0x8f2040c8,
      0x4f3aff82, 0x55e30c8d, 0xaa73eb01, 0x921291c5, 0xc71c692e, 0x7853fbc9,
      0xb6e99a57, 0x777c932d, 0xedbf4c50, 0x1f1adcd6,
  };
  static const uint32_t kCtsRsaPssSha256Sig[kRsa2048NumWords] = {
      0xdc164c52, 0xf90c1fd6, 0xb87600a2, 0x16fbb9e9, 0x83b9149e, 0x22907e8b,
      0x32ad128f, 0x29151d86, 0x46dcff7b, 0x8b27c1b9, 0xd5617bae, 0x11eba649,
      0x1e408e80, 0xa8aca97d, 0xb76d4ed5, 0xfb895c6c, 0x4653e124, 0x617cdf57,
      0x00f7a4f2, 0x346e2019, 0x11d01582, 0x9fc4baf6, 0xff7ee723, 0x1f157137,
      0xd36b699d, 0xfba62720, 0x1152c81f, 0x8ae80ce9, 0x56a0da8a, 0x3b7497d5,
      0xa7b2009f, 0x559be587, 0xe768d2d2, 0x4d46ba7e, 0x1daa4c58, 0xd9c6f4c4,
      0xb2ac5e71, 0x5910a786, 0x674c04cd, 0xf243fab1, 0xcbe00a1b, 0x136aa629,
      0x870f290d, 0x68c28a54, 0xf1f37422, 0x61cc6f87, 0x2d80e624, 0x6f5710a0,
      0x16b0fd98, 0x4e94de48, 0xe94e1c48, 0x33393293, 0xcc8ff38f, 0xbad57995,
      0x867821ef, 0x1ad691f8, 0x5b597231, 0x305c759b, 0x21b4daae, 0xee0d61e6,
      0x95c1aa8a, 0xc7caa0c3, 0xa8e813b4, 0x6f0f744f,
  };
  otcrypto_const_byte_buf_t cts_msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsSigMsg, sizeof(kCtsSigMsg));
  TRY(otcrypto_sha2_256(&cts_msg_buf, &sha256_digest));

  otcrypto_const_word32_buf_t key1_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaKey1Modulus, kRsa2048NumWords);
  otcrypto_const_word32_buf_t key1_d0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaKey1PrivExp, kRsa2048NumWords);
  uint32_t zero_share[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t key1_d1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, zero_share, kRsa2048NumWords);

  public_key = (otcrypto_unblinded_key_t){
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &key1_mod,
                                        &public_key));
  private_key = (otcrypto_blinded_key_t){
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeRsaSignPkcs,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob = priv_blob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &key1_mod, &key1_d0, &key1_d1, &private_key));

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  TRY(otcrypto_rsa_sign(&private_key, sha256_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  TRY_CHECK_ARRAYS_EQ(sig, kCtsRsaPkcs1Sha256Sig, kRsa2048NumWords);

  otcrypto_const_word32_buf_t kat_sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaPkcs1Sha256Sig, kRsa2048NumWords);
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, sha256_digest, kOtcryptoRsaPaddingPkcs,
                          &kat_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  public_key.key_mode = kOtcryptoKeyModeRsaSignPss;
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &key1_mod,
                                        &public_key));
  otcrypto_const_word32_buf_t kat_pss_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaPssSha256Sig, kRsa2048NumWords);
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, sha256_digest, kOtcryptoRsaPaddingPss,
                          &kat_pss_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Android CTS `SignatureTest.java:288-330, 756` (`LONG_MSG_KAT_SIGNATURES` /
  // `testLongMsgKat` over `3 * 1024 * 1024 + 123` bytes generated via
  // `TestUtils.generateLargeKatMsg(kCtsSigMsg, ...)`): Verify StrongBox
  // `SHA256withRSA` and `SHA256withRSA/PSS` KAT signatures with `kCtsRsaKey1`.
  static const uint32_t kCtsSigLongMsgSha256Words[256 / 32] = {
      0x4fddb69b, 0x635b84a3, 0x2ee8a8c5, 0x6c4c6ba9,
      0x4552820f, 0x36f4d81d, 0x75b8a434, 0x4124bc8b,
  };
  static const uint32_t kCtsRsaLongMsgPkcs1Sha256Sig[kRsa2048NumWords] = {
      0x35ee710a, 0x0a24d0a8, 0x7c18d189, 0x73c8b174, 0x8b54e10b, 0x6c7cbb55,
      0x7549cebf, 0x48a9253b, 0xc206472e, 0x615b4150, 0x466188d1, 0x99e67c7b,
      0xe3e6e2fc, 0x57b93fbc, 0xd1bc090d, 0xe10f0736, 0xa3bd9961, 0xab1f8bfd,
      0x4ad20e88, 0x93a3b135, 0xefec2aa4, 0x9ea80b5c, 0xef7a608d, 0x5e88a30e,
      0xc32e0cdc, 0xccb6e8ff, 0xc35ea879, 0x5707d71b, 0x05894e4e, 0xdeddbe5d,
      0xc5b6eca3, 0x4cf593ec, 0x53ef2283, 0x9bd1b451, 0x877bda17, 0x25e8bb9b,
      0xaa4708f9, 0x527b11fc, 0xbf6f1f85, 0x338c2be4, 0x6f3b8685, 0x9c939fd8,
      0x5c452796, 0xd96357da, 0x19adae67, 0x43444385, 0x7d4e9667, 0x7d3e01c7,
      0xa7996250, 0xc62e8007, 0x3e6ac1d6, 0x65f35cb5, 0x7045ea69, 0x245ed276,
      0xf8a73226, 0x263bef2e, 0x98de5c85, 0x8f8bbceb, 0xe70da79f, 0x99e1edec,
      0x2f2b0fc8, 0x1abda98a, 0x7dedf3eb, 0x529c7087,
  };
  static const uint32_t kCtsRsaLongMsgPssSha256Sig[kRsa2048NumWords] = {
      0x70387a2e, 0xc6dce30d, 0x8e0b4905, 0x4d3521e9, 0xa25bd32b, 0x113b324f,
      0x8073aa00, 0xc9bd6178, 0x96ab0567, 0x50099317, 0x6e486a74, 0x7559355b,
      0x6df40720, 0xc68134ba, 0x38468fa2, 0xe49ad87f, 0xb0f6da17, 0x669f7609,
      0xe8bc3335, 0xa4a88f3f, 0x1304b359, 0x33c53db0, 0x9276b0bd, 0xd5e5b71c,
      0x10a7b11c, 0xefd25cc8, 0x4cc977de, 0x0d94a25b, 0x00052962, 0x173095ea,
      0x6964c5ad, 0x0af6d09d, 0x93ce12c3, 0x4970cd5e, 0xabaca17b, 0xf57636cd,
      0x4114e9dc, 0xa5b09218, 0xa7dd6d51, 0xc622fdfc, 0x9308c4fe, 0x7210b53f,
      0x924860d2, 0xa286e545, 0x73f2721b, 0xb92ed72e, 0x874a92d4, 0x6baa6014,
      0xaab6a98a, 0x60759f8c, 0x538dc2ad, 0xbc8bf725, 0x86d1f81f, 0x2e8cd1bb,
      0x94a873dd, 0x69013571, 0x989368ae, 0x9f02c88a, 0xa73139ea, 0x3da18cfd,
      0x398b38b9, 0x07b3ad83, 0x93a67142, 0x5a8c0ae5,
  };
  otcrypto_hash_digest_t long_msg_sha256_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = (uint32_t *)kCtsSigLongMsgSha256Words,
      .len = ARRAYSIZE(kCtsSigLongMsgSha256Words),
  };
  public_key.key_mode = kOtcryptoKeyModeRsaSignPkcs;
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &key1_mod,
                                        &public_key));
  TRY(otcrypto_rsa_sign(&private_key, long_msg_sha256_digest,
                        kOtcryptoRsaPaddingPkcs, &sig_buf));
  TRY_CHECK_ARRAYS_EQ(sig, kCtsRsaLongMsgPkcs1Sha256Sig, kRsa2048NumWords);
  otcrypto_const_word32_buf_t kat_long_pkcs_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t,
                        kCtsRsaLongMsgPkcs1Sha256Sig, kRsa2048NumWords);
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, long_msg_sha256_digest,
                          kOtcryptoRsaPaddingPkcs, &kat_long_pkcs_buf,
                          &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  public_key.key_mode = kOtcryptoKeyModeRsaSignPss;
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &key1_mod,
                                        &public_key));
  otcrypto_const_word32_buf_t kat_long_pss_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kCtsRsaLongMsgPssSha256Sig,
                        kRsa2048NumWords);
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, long_msg_sha256_digest,
                          kOtcryptoRsaPaddingPss, &kat_long_pss_buf,
                          &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Verify `NONEwithRSA` (`SignatureTest.java:132-139`) over the 23-byte
  // `kCtsSigMsg` directly using `kOtcryptoKeyModeRsaSignPkcs` +
  // `kOtcryptoRsaPaddingPkcs` and `kOtcryptoHashModeNull` (`.len = 23` bytes):
  uint32_t cts_none_msg_words[ceil_div(sizeof(kCtsSigMsg), sizeof(uint32_t))];
  memset(cts_none_msg_words, 0, sizeof(cts_none_msg_words));
  memcpy(cts_none_msg_words, kCtsSigMsg, sizeof(kCtsSigMsg));
  otcrypto_hash_digest_t cts_none_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = cts_none_msg_words,
      .len = sizeof(kCtsSigMsg),
  };
  TRY(construct_custom_rsa2048_keypair(kCtsRsaKey1Modulus, kCtsRsaKey1PrivExp,
                                       kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                       &public_key, priv_blob, &private_key));
  TRY(otcrypto_rsa_sign(&private_key, cts_none_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  TRY_CHECK_ARRAYS_EQ(sig, kCtsRsaNoneSig, kRsa2048NumWords);
  otcrypto_const_word32_buf_t kat_none_sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaNoneSig, kRsa2048NumWords);
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, cts_none_digest, kOtcryptoRsaPaddingPkcs,
                          &kat_none_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:5410` —
 *     `TEST_P(EncryptionOperationsTest, RsaNoPaddingSuccess)`
 *   - `KeyMintTest.cpp:5525` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepInvalidDigest)`
 *   - `KeyMintTest.cpp:5591` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepWithMGFDigestSuccess)`
 *   - `KeyMintTest.cpp:5801` —
 *     `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)`
 *   - `CipherTest.java:192-211, 398, 956, 1036`
 *   - `RSACipherTest.java:71-265` (`StrongboxRSACipherTest`)
 *
 * On StrongBox (`SecurityLevel::STRONGBOX`), `ValidDigests(false, true)` is
 * `{Digest::SHA_2_256}` (`RsaOaepDecryptWithWrongDigest` is skipped on
 * StrongBox at `KeyMintTest.cpp:5561`).
 */
static status_t rsa_vts_encryption_modes_test(void) {
  LOG_INFO(
      "Testing StrongBox EncryptionOperationsTest.RsaNoPadding*, RsaPkcs1*, "
      "RsaOaep* (SHA-256)");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t ciphertext[kRsa2048NumWords];
  otcrypto_word32_buf_t ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ciphertext, ARRAYSIZE(ciphertext));
  otcrypto_const_word32_buf_t const_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ciphertext, ARRAYSIZE(ciphertext));
  otcrypto_const_byte_buf_t empty_label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_const_byte_buf_t label_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kTestLabel, kTestLabelLen);

  uint8_t decrypted[kRsa2048NumBytes];
  size_t decrypted_len = 0;

  // 1. PKCS#1 v1.5 Encryption (`kOtcryptoKeyModeRsaEncryptPkcs`):
  // Test 0-byte empty plaintext
  // (`CipherTest.testEmptyPlaintextEncryptsAndDecrypts` &
  // `KeyMintTest.cpp:5801`), max message length (245B,
  // `CipherTest.testMaxSizedPlaintextSupported`), and rejection of 246B
  // (`CipherTest.testLargerThanMaxSizedPlaintextRejected`).
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_const_byte_buf_t empty_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_byte_buf_t pkcs_pt_out = OTCRYPTO_MAKE_BUF(
      otcrypto_byte_buf_t, decrypted, kMaxPkcs1v15PayloadBytes);
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &empty_pt,
                           &empty_label, &ct_buf));
  decrypted_len = 999;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &pkcs_pt_out, &decrypted_len));
  TRY_CHECK(decrypted_len == 0);

  uint8_t max_pkcs_msg[kMaxPkcs1v15PayloadBytes];
  for (size_t i = 0; i < sizeof(max_pkcs_msg); ++i) {
    max_pkcs_msg[i] = (uint8_t)(i ^ 0xa5);
  }
  otcrypto_const_byte_buf_t max_pkcs_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, max_pkcs_msg, sizeof(max_pkcs_msg));

  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &max_pkcs_in,
                           &empty_label, &ct_buf));
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &pkcs_pt_out, &decrypted_len));
  TRY_CHECK(decrypted_len == sizeof(max_pkcs_msg));
  TRY_CHECK_ARRAYS_EQ(decrypted, max_pkcs_msg, decrypted_len);

  uint8_t too_long_pkcs[kMaxPkcs1v15PayloadBytes + 1] = {0};
  otcrypto_const_byte_buf_t too_long_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, too_long_pkcs, sizeof(too_long_pkcs));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull,
                                 &too_long_in, &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 2. Raw RSA Encryption (`kOtcryptoKeyModeRsaRaw`):
  // Left-padding `kTestMessage` with leading `0x00` bytes in big-endian integer
  // order corresponds to reversing `kTestMessage` into the least-significant
  // `kTestMessageLen` bytes of the little-endian `raw_pt` buffer.
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaRaw, pub_data, &public_key,
                                priv_blob, &private_key));
  uint8_t raw_pt[kRsa2048NumBytes] = {0};
  for (size_t i = 0; i < kTestMessageLen; ++i) {
    raw_pt[i] = kTestMessage[kTestMessageLen - 1 - i];
  }
  otcrypto_const_byte_buf_t raw_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, raw_pt, sizeof(raw_pt));
  otcrypto_byte_buf_t raw_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));

  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &raw_in,
                           &empty_label, &ct_buf));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == kRsa2048NumBytes);
  TRY_CHECK_ARRAYS_EQ(decrypted, raw_pt, kRsa2048NumBytes);

  // 3. StrongBox RSA-OAEP with SHA-256 (`RsaOaepWithMGFDigestSuccess`,
  // `KeyMintTest.cpp:5591`, `CipherTest.testEmptyPlaintextEncryptsAndDecrypts`,
  // `CipherTest.testMaxSizedPlaintextSupported`, and
  // `CipherTest.testLargerThanMaxSizedPlaintextRejected`):
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptOaep, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_const_byte_buf_t msg_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kTestMessage, kTestMessageLen);

  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256, &msg_in,
                           &label_buf, &ct_buf));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256, &const_ct_buf,
                           &label_buf, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == kTestMessageLen);
  TRY_CHECK_ARRAYS_EQ(decrypted, kTestMessage, kTestMessageLen);

  // Decrypting with a mismatched OAEP label must fail.
  TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256,
                                 &const_ct_buf, &empty_label, &raw_out,
                                 &decrypted_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 0-byte OAEP-SHA256 round-trip
  // (`CipherTest.testEmptyPlaintextEncryptsAndDecrypts`):
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256, &empty_pt,
                           &empty_label, &ct_buf));
  decrypted_len = 999;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == 0);

  // Max OAEP-SHA256 payload (190B, `CipherTest.testMaxSizedPlaintextSupported`)
  // and rejection of 191B
  // (`CipherTest.testLargerThanMaxSizedPlaintextRejected`):
  uint8_t max_oaep_msg[kMaxOaepSha256PayloadBytes];
  for (size_t i = 0; i < sizeof(max_oaep_msg); ++i) {
    max_oaep_msg[i] = (uint8_t)(i ^ 0x3c);
  }
  otcrypto_const_byte_buf_t max_oaep_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, max_oaep_msg, sizeof(max_oaep_msg));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256, &max_oaep_in,
                           &empty_label, &ct_buf));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == sizeof(max_oaep_msg));
  TRY_CHECK_ARRAYS_EQ(decrypted, max_oaep_msg, sizeof(max_oaep_msg));

  uint8_t too_long_oaep[kMaxOaepSha256PayloadBytes + 1] = {0};
  otcrypto_const_byte_buf_t too_long_oaep_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, too_long_oaep, sizeof(too_long_oaep));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256,
                                 &too_long_oaep_in, &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // KeyMintTest.cpp:5497 (`RsaOaepSuccess`) & 5525 (`RsaOaepInvalidDigest`):
  // - OAEP encryption is randomized (`ciphertext1 != ciphertext2`).
  uint32_t ciphertext2[kRsa2048NumWords];
  otcrypto_word32_buf_t ct2_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ciphertext2, ARRAYSIZE(ciphertext2));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256, &msg_in,
                           &empty_label, &ct_buf));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeSha256, &msg_in,
                           &empty_label, &ct2_buf));
  TRY_CHECK(memcmp(ciphertext, ciphertext2, sizeof(ciphertext)) != 0);

  // - `RsaOaepInvalidDigest`: OAEP with `Digest::NONE`
  //   (`kOtcryptoHashModeNull`) fails with `OTCRYPTO_BAD_ARGS`.
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &msg_in,
                                 &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);

  // 4. Android CTS `CipherTest.java:192-211` (`KAT_VECTORS`) using
  // `R.raw.rsa_key2_pkcs8` for StrongBox (`RSA/ECB/NoPadding` and
  // `RSA/ECB/PKCS1Padding`):
  static const uint32_t kCtsRsaNoPadPt[kRsa2048NumWords] = {
      0xb9d15222, 0xeb96060e, 0x2fb101b0, 0x1724a569, 0x006d34f1, 0x4323ccb8,
      0x153a98fd, 0xabc76e4e, 0x32887db2, 0xd48ea768, 0xd558c38f, 0x0050c499,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000,
  };
  static const uint32_t kCtsRsaNoPadCt[kRsa2048NumWords] = {
      0xfa650697, 0xede206ac, 0xd9fbaadd, 0x5ddebf92, 0x6a7acbe1, 0x9efdeed8,
      0xe2bb3376, 0xd7188fe7, 0xe56092ee, 0x5914ce4b, 0xddac7584, 0x9636d67c,
      0x2e90041e, 0xf8ee427f, 0x9e3b6fe6, 0x1da22902, 0x337b1603, 0xc333d131,
      0xd6ac6fd6, 0x73cdec88, 0xb97c0565, 0x0aafbb9e, 0x63417bc0, 0x01278c66,
      0x6cf21444, 0x264896fb, 0x8c56eeff, 0x1e5c3aea, 0xa0fec4d0, 0xa5a5dac1,
      0xd2a2f98e, 0x92dc3d32, 0xb07f00b2, 0x99d8de02, 0x838c0d43, 0x4cc2dd78,
      0x475afeba, 0xd9ec750f, 0x7de7bfe9, 0xe7e505dc, 0x3df0d98b, 0x7c343295,
      0xe41297b8, 0xfb0ac585, 0x4ed17099, 0xa03f95e1, 0xa51e6293, 0x32778592,
      0x5cc69ced, 0x5f5ba27e, 0x5c13dc40, 0x098318e5, 0x25e6ae5e, 0xb1654aab,
      0x592ede29, 0xd822d369, 0x223e3f78, 0xc67cf535, 0xe26148d7, 0xb1b8ef8e,
      0x80bbc0cb, 0xb3f23276, 0x61e98d0a, 0x349b1d50,
  };
  static const uint8_t kCtsRsaPkcs1Pt[50] = {
      0xae, 0xd8, 0xcd, 0x94, 0xf3, 0x5b, 0x2a, 0x54, 0xcd, 0xd3,
      0xed, 0x77, 0x14, 0x82, 0xbd, 0x87, 0xe2, 0x56, 0xb9, 0x95,
      0x40, 0x85, 0x58, 0xfb, 0x82, 0xe5, 0xd4, 0x75, 0xd1, 0xee,
      0x54, 0x71, 0x14, 0x72, 0xf8, 0x99, 0xad, 0x6c, 0xbb, 0x68,
      0x47, 0x99, 0xe5, 0x2f, 0xf1, 0xd5, 0x7c, 0xbc, 0x39, 0xf4,
  };
  static const uint32_t kCtsRsaPkcs1Ct[kRsa2048NumWords] = {
      0xdbfd5978, 0xe20fb1a9, 0x37a74df3, 0x2ef82fbe, 0xcf7b678a, 0x43da6e1d,
      0x75c9f5b1, 0x444b011d, 0x0589d7d0, 0x60557a0c, 0xb47e43e9, 0x9fd6e752,
      0xb98ad797, 0x945d6491, 0xe46a939a, 0xabae1475, 0x774b7486, 0x1958e5a0,
      0x113d2489, 0x2213c1cc, 0x99e86b0b, 0x82cf484d, 0xc68ace91, 0x9c199ee2,
      0x0f83c4f8, 0xcbb2642e, 0xcabd53a2, 0x5010834f, 0x59651433, 0xd9ccec4c,
      0x6f59f351, 0x8928949b, 0x4351d060, 0x19c628fd, 0x12113167, 0xadd20f52,
      0x3f9fb74a, 0x413d2706, 0x8a242737, 0xcd494a5c, 0xb7f39079, 0x226bc806,
      0x7530c162, 0x33f24b72, 0x420d0ea4, 0x49061319, 0x51cb4caa, 0xed5b70da,
      0x157af0d2, 0xdbe3103c, 0x2df9c703, 0xb95a2df0, 0xc5eca522, 0xcb267938,
      0x4d3cfde3, 0xeb1e6b5f, 0xe8993e73, 0x559087d6, 0x71393cf6, 0xcf90c89f,
      0xea661318, 0x31d2b595, 0x294dd3ea, 0x64148dee,
  };
  otcrypto_const_word32_buf_t key2_mod = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaKey2Modulus, kRsa2048NumWords);
  otcrypto_const_word32_buf_t key2_d0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaKey2PrivExp, kRsa2048NumWords);
  uint32_t key2_zero_share[kRsa2048NumWords] = {0};
  otcrypto_const_word32_buf_t key2_d1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, key2_zero_share, kRsa2048NumWords);

  // 4a. `KAT_VECTORS["RSA/ECB/NoPadding"]` (`CipherTest.java:192-201`):
  public_key = (otcrypto_unblinded_key_t){
      .key_mode = kOtcryptoKeyModeRsaRaw,
      .key_length = kOtcryptoRsa2048PublicKeyBytes,
      .key = pub_data,
  };
  TRY(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize2048, &key2_mod,
                                        &public_key));
  private_key = (otcrypto_blinded_key_t){
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeRsaRaw,
              .key_length = kOtcryptoRsa2048PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob = priv_blob,
      .keyblob_length = kOtcryptoRsa2048PrivateKeyblobBytes,
  };
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &key2_mod, &key2_d0, &key2_d1, &private_key));

  otcrypto_const_byte_buf_t cts_nopad_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)kCtsRsaNoPadPt,
      sizeof(kCtsRsaNoPadPt));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &cts_nopad_in,
                           &empty_label, &ct_buf));
  TRY_CHECK_ARRAYS_EQ(ciphertext, kCtsRsaNoPadCt, kRsa2048NumWords);
  otcrypto_const_word32_buf_t cts_nopad_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaNoPadCt, kRsa2048NumWords);
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull,
                           &cts_nopad_ct_buf, &empty_label, &raw_out,
                           &decrypted_len));
  TRY_CHECK(decrypted_len == kRsa2048NumBytes);
  TRY_CHECK_ARRAYS_EQ(decrypted, (const uint8_t *)kCtsRsaNoPadPt,
                      kRsa2048NumBytes);

  // 4b. `KAT_VECTORS["RSA/ECB/PKCS1Padding"]` (`CipherTest.java:202-211`):
  private_key.config.key_mode = kOtcryptoKeyModeRsaEncryptPkcs;
  TRY(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize2048, &key2_mod, &key2_d0, &key2_d1, &private_key));
  otcrypto_const_word32_buf_t cts_pkcs1_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaPkcs1Ct, kRsa2048NumWords);
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull,
                           &cts_pkcs1_ct_buf, &empty_label, &pkcs_pt_out,
                           &decrypted_len));
  TRY_CHECK(decrypted_len == sizeof(kCtsRsaPkcs1Pt));
  TRY_CHECK_ARRAYS_EQ(decrypted, kCtsRsaPkcs1Pt, sizeof(kCtsRsaPkcs1Pt));

  // 4c. Android CTS `RSACipherTest.java:118-265` (`StrongboxRSACipherTest` raw
  // RSA boundary plaintexts `1`, `n - 1`, `n`, `n + 1`, and oversized inputs
  // using `R.raw.rsa_key8_2048_pkcs8`):
  TRY(construct_custom_rsa2048_keypair(kCtsRsaKey8Modulus, kCtsRsaKey8PrivExp,
                                       kOtcryptoKeyModeRsaRaw, pub_data,
                                       &public_key, priv_blob, &private_key));
  // Boundary: m = 1 (256B) -> encrypt + decrypt round-trip recovers 1
  // (`RSACipherTest.java:118`
  // `testNoPaddingOnePlaintextEncryptsAndDecryptsToOne`)
  uint8_t m_one_256b[kRsa2048NumBytes] = {0};
  m_one_256b[0] = 0x01;
  otcrypto_const_byte_buf_t one_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, m_one_256b, sizeof(m_one_256b));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &one_in,
                           &empty_label, &ct_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)ciphertext, m_one_256b,
                      sizeof(m_one_256b));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == kRsa2048NumBytes);
  TRY_CHECK_ARRAYS_EQ(decrypted, m_one_256b, sizeof(m_one_256b));

  // Boundary: m = n - 1 -> encrypt + decrypt round-trip recovers n - 1
  uint32_t n_minus_1[kRsa2048NumWords];
  memcpy(n_minus_1, kCtsRsaKey8Modulus, sizeof(n_minus_1));
  n_minus_1[0] -= 1u;  // kCtsRsaKey8Modulus is odd, so word 0 >= 1
  otcrypto_const_byte_buf_t nm1_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)n_minus_1, sizeof(n_minus_1));
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &nm1_in,
                           &empty_label, &ct_buf));
  decrypted_len = 0;
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &raw_out, &decrypted_len));
  TRY_CHECK(decrypted_len == kRsa2048NumBytes);
  TRY_CHECK_ARRAYS_EQ(decrypted, (const uint8_t *)n_minus_1, sizeof(n_minus_1));

  // Boundary: m = n and m = n + 1 must be rejected with OTCRYPTO_BAD_ARGS on
  // both encrypt and decrypt (`RSACipherTest.java:186-265`).
  otcrypto_const_byte_buf_t n_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)kCtsRsaKey8Modulus,
      sizeof(kCtsRsaKey8Modulus));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &n_in,
                                 &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_const_word32_buf_t n_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaKey8Modulus, kRsa2048NumWords);
  TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &n_ct_buf,
                                 &empty_label, &raw_out, &decrypted_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  uint32_t n_plus_1[kRsa2048NumWords];
  memcpy(n_plus_1, kCtsRsaKey8Modulus, sizeof(n_plus_1));
  n_plus_1[0] += 1u;
  otcrypto_const_byte_buf_t np1_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)n_plus_1, sizeof(n_plus_1));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &np1_in,
                                 &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);
  otcrypto_const_word32_buf_t np1_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, n_plus_1, kRsa2048NumWords);
  TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull,
                                 &np1_ct_buf, &empty_label, &raw_out,
                                 &decrypted_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  // Oversized > 256-byte input rejected on encrypt and decrypt
  // (`CipherTest.testLargerThanMaxSizedPlaintextRejected` /
  // `RSACipherTest.testNoPaddingLargerThanModulusPlaintextRejected`).
  uint8_t oversized_raw_pt[kRsa2048NumBytes + 1] = {0};
  otcrypto_const_byte_buf_t oversized_raw_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, oversized_raw_pt, sizeof(oversized_raw_pt));
  TRY_CHECK(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull,
                                 &oversized_raw_in, &empty_label, &ct_buf)
                .value == OTCRYPTO_BAD_ARGS.value);
  uint32_t oversized_raw_ct[kRsa2048NumWords + 1] = {0};
  otcrypto_const_word32_buf_t oversized_raw_ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, oversized_raw_ct,
                        ARRAYSIZE(oversized_raw_ct));
  TRY_CHECK(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull,
                                 &oversized_raw_ct_buf, &empty_label, &raw_out,
                                 &decrypted_len)
                .value == OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:240-249` —
 *     `KAT_VECTORS["RSA/ECB/OAEPWithSHA-256AndMGF1Padding"]`
 *   - `KeyMintTest.cpp:5463` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepSuccess)`
 *   - `KeyMintTest.cpp:5662` —
 *     `TEST_P(EncryptionOperationsTest, RsaOaepMGFDigestDefaultSuccess)`
 *
 * Verifies RSA-OAEP decryption using `SHA-256` as the main digest with
 * `MGF1-SHA1` (`kOtcryptoKeyModeRsaEncryptOaepMgfSha1`).
 */
static status_t rsa_cts_oaep_sha256_mgf1_sha1_kat_test(void) {
  LOG_INFO(
      "Testing CTS KAT_VECTORS[RSA/ECB/OAEPWithSHA-256AndMGF1Padding] & VTS "
      "RsaOaepMGFDigestDefaultSuccess");
  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  TRY(construct_custom_rsa2048_keypair(kCtsRsaKey2Modulus, kCtsRsaKey2PrivExp,
                                       kOtcryptoKeyModeRsaEncryptOaepMgfSha1,
                                       pub_data, &public_key, priv_blob,
                                       &private_key));
  otcrypto_const_word32_buf_t cts_oaep_sha256_ct_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsRsaOaepSha256Ct, kRsa2048NumWords);
  otcrypto_const_byte_buf_t empty_label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  uint8_t decrypted[kRsa2048NumBytes];
  otcrypto_byte_buf_t raw_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, sizeof(decrypted));
  size_t decrypted_len = 0;

  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeSha256,
                           &cts_oaep_sha256_ct_buf, &empty_label, &raw_out,
                           &decrypted_len));
  TRY_CHECK(decrypted_len == sizeof(kCtsRsaOaepSha256Pt));
  TRY_CHECK_ARRAYS_EQ(decrypted, kCtsRsaOaepSha256Pt,
                      sizeof(kCtsRsaOaepSha256Pt));
  return OK_STATUS();
}

/**
 * Source:
 *   - `CipherTest.java:398` — `testEmptyPlaintextEncryptsAndDecrypts`
 *   - `KeyMintTest.cpp:5801` —
 *     `TEST_P(EncryptionOperationsTest, RsaPkcs1Success)` (0-byte message
 *     decryption into a caller buffer smaller than `k - 11 = 245` bytes)
 */
static status_t rsa_cts_pkcs1_v15_empty_plaintext_short_buf_test(void) {
  LOG_INFO(
      "Testing Android CTS testEmptyPlaintextEncryptsAndDecrypts & KeyMint VTS "
      "RsaPkcs1Success (0-byte PKCS#1 v1.5 decrypt into < 245B buffer)");

  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t ct[kRsa2048NumWords];
  otcrypto_word32_buf_t ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ct, ARRAYSIZE(ct));
  otcrypto_const_word32_buf_t const_ct_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, ct, ARRAYSIZE(ct));

  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaEncryptPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_const_byte_buf_t empty_pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_const_byte_buf_t empty_label =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_rsa_encrypt(&public_key, kOtcryptoHashModeNull, &empty_pt,
                           &empty_label, &ct_buf));

  // Decrypting a 0-byte PKCS#1 v1.5 plaintext into a 64-byte output buffer
  // should succeed (`OTCRYPTO_OK` with `decrypted_len == 0`).
  uint8_t decrypted[kRsa2048NumBytes];
  size_t decrypted_len = 999;
  otcrypto_byte_buf_t small_out =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, decrypted, 64);
  TRY(otcrypto_rsa_decrypt(&private_key, kOtcryptoHashModeNull, &const_ct_buf,
                           &empty_label, &small_out, &decrypted_len));
  TRY_CHECK(decrypted_len == 0);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3321` — `TEST_P(SigningOperationsTest, RsaNoDigest)`
 *     (0-byte message signing and verification with `RSA_PKCS1_1_5_SIGN` +
 *     `Digest::NONE`)
 */
static status_t rsa_vts_signing_zero_length_no_digest_test(void) {
  LOG_INFO(
      "Testing KeyMint VTS SigningOperationsTest.RsaNoDigest (0-byte message)");

  uint32_t pub_data[ceil_div(kOtcryptoRsa2048PublicKeyBytes, sizeof(uint32_t))];
  uint32_t priv_blob[ceil_div(kOtcryptoRsa2048PrivateKeyblobBytes,
                              sizeof(uint32_t))];
  otcrypto_unblinded_key_t public_key;
  otcrypto_blinded_key_t private_key;

  uint32_t sig[kRsa2048NumWords];
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  // KeyMint VTS `SigningOperationsTest.RsaNoDigest` (`KeyMintTest.cpp:3321`)
  // 0-byte message: `otcrypto_rsa_sign` and `otcrypto_rsa_verify` with
  // `kOtcryptoRsaPaddingPkcs` + `kOtcryptoHashModeNull` and `len = 0` should
  // succeed (`OTCRYPTO_OK`).
  TRY(construct_rsa2048_keypair(kOtcryptoKeyModeRsaSignPkcs, pub_data,
                                &public_key, priv_blob, &private_key));
  otcrypto_hash_digest_t empty_raw_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = NULL,
      .len = 0,
  };
  TRY(otcrypto_rsa_sign(&private_key, empty_raw_digest, kOtcryptoRsaPaddingPkcs,
                        &sig_buf));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_rsa_verify(&public_key, empty_raw_digest,
                          kOtcryptoRsaPaddingPkcs, &const_sig_buf, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, rsa_vts_signing_no_digest_and_raw_test);
  EXECUTE_TEST(result, rsa_vts_signing_pkcs1_and_pss_hashes_test);
  EXECUTE_TEST(result, rsa_vts_encryption_modes_test);
  EXECUTE_TEST(result, rsa_cts_oaep_sha256_mgf1_sha1_kat_test);
  EXECUTE_TEST(result, rsa_cts_pkcs1_v15_empty_plaintext_short_buf_test);
  EXECUTE_TEST(result, rsa_vts_signing_zero_length_no_digest_test);

  // Note: The following VTS/CTS cases require caller/wrapper pre-formatting and
  // are documented in `README.md` (Item 5):
  // - Short raw RSA inputs (`KeyMintTest.cpp:3359` `RsaTooShortMessage`,
  //   `KeyMintTest.cpp:5439` `RsaNoPaddingShortMessage`,
  //   `RSACipherTest.java:132`): the wrapper zero-pads non-zero short messages
  //   to the full modulus length before calling `otcrypto_rsa_sign` /
  //   `otcrypto_rsa_encrypt`.
  // - All-zero raw RSA plaintext (`RSACipherTest.java:86` `m = 0` and
  //   `CipherTest.java:398` 0-byte `RSA/ECB/NoPadding`): `otcrypto`
  //   (`run_rsa.c`) intentionally rejects all-zero modexp outputs (`0^e mod n
  //   == 0`) with `OTCRYPTO_BAD_ARGS`.

  return status_ok(result);
}
