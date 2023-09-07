// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module for status messages.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  kRsa4096NumBytes = 4096 / 8,
  kRsa4096NumWords = kRsa4096NumBytes / sizeof(uint32_t),
};

// Note: The private key and valid signatures for this test were generated
// out-of-band using the PyCryptodome Python library.

// Test RSA-4096 key pair:
// e = 65537
// n =
// 0x923d26b1b8100867c52ceccbb7b12778bb56c41e74a00192f5cff3d6ca455764149f474abdff524f8711d18bca9ec1c8a911acb9f3b55b92c93741ae5096eb55ee537161caa24b43b7975de681890d9794274031f7d34763e616c66878c110562797e007df176908c5c7c09e28f41846a83522b7a080a8dee6f54599c11a46110733ddacda83238c5e2494c3a9db50ec2ac2bfcf456d1b349a20f3667d4b42e4301ba27152b6aeb4910a869848ba51ca6c4bc2bce4605201fb97013876b81c66f41e8e1a164bdfe9cf2c938d741a0a139a16aa5e371e6534f7b2fe46e9366e3fd94c6f9a84137166f9795da6a341b921ae584a1c5d772fa168ae9ea592da78749ead0010678acef1f405ca0387bf02a1d214c97078fc971eb9543c035b26d7fb59c05b949d589400456b541d1f538ee569f8e760ef593e46bf4a036b217125254a690b240d87195eb02f876604c40c5f43957974cc710705f63d8d4495e0d71a0b87bef169c526075428afc5d476a75343a405d3065717ba3cdee7b26398b8b1a272f6768ad109a2ebead54f19567c96caacc7d0f9ae495aff3fed73dea0d12f3a9c60c474fe316c964c7c044ab8c5fcc7b2b40c8dfeae93cf348dfbef92361d4f473ba5f9699bf22ab3eb21f22b2197a970c3dcd33d1707a86ad866b1d4b69cf071b30b17488f537c4ceeb0ea50031cde80fc8b02cdc82c85c4bdcf3114efe5
// d =
// 0x19aacb83965d940818a2c3b616d9ec6663a53d3b66375e475bc721d271829dadd673c558d043c3bfeb225cbfd732a9ab0d47a9a422ab12754f45584d1ede7a54450616c8b5fee9cc6b2911655f977d4ffd442d5f87d2a8bd5739689e1611b6cb145c730916a63e7c787050b5c1d4e3fce4d19cb413a2f960d4333901dd537df847a61a129870bb78cbde4a51145b46d708c35154b1280f061ac64d4a5013f95be138bc787ceeccf7aadc68d6ca2f0fa38282029e524c38a099f6bd535a7d02992c603f8b431e12a130486fe67c3a04ca3f799a71fa652698d71feec2e5f47481d6e334546fb994e620c3e544d5f33769fab68add732733f035d62e48bbdf861417fecf98658a898c297fec029ea004b708edc6ec008462ec7a62418a56bc03a553d53ac463a211a93a019ce8bc4e07269c7269f61b146fdb73fb2898e9371f6d087d75f53409f25ccda8258a7955470feda00eb93130ab1beeb31968ff0f46e59e8950467af1eeb7fb339c321aa75fe8f87aa3ccbd0107506a6ed6f1e3a10c0ef29cbee4e62df4f64eb8bd8aa40c8a129d1bf875ea48ce7801204058cf40085e248f7d36f3c16658252a9da39255f7addb82a4c11707763eccb95bca1fc075d6a6bca8d4db656795f0f0ec3a0a86efb9ed1cf5db010cc1af90a218e04a977ff1e077dea92fcbfb38bdbc9c786b11c61ded4cacbe4c0f18d02109108d2605e651

// Modulus (n) in little-endian form.
static uint32_t kTestModulus[kRsa4096NumWords] = {
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
static uint32_t kTestPrivateExponent[kRsa4096NumWords] = {
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
static uint32_t kTestPublicExponent = 65537;

// Message data for testing.
static const unsigned char kTestMessage[] = "Test message.";
static const size_t kTestMessageLen = sizeof(kTestMessage) - 1;

// Valid signature of `kTestMessage` from the test private key, using PKCS#1
// v1.5 padding and SHA-512 as the hash function.
static const uint32_t kValidSignaturePkcs1v15[kRsa4096NumWords] = {
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

// Valid signature of `kTestMessage` from the test private key, using PSS
// padding and SHA-512 as the hash function.
static const uint32_t kValidSignaturePss[kRsa4096NumWords] = {
    0xac65bc2f, 0x7022bce6, 0x76849939, 0xba21c651, 0xdfb70b15, 0x7ae994ca,
    0x05eae1d1, 0x57ca0aea, 0xfefb90c5, 0x59357a95, 0x9d79703c, 0x352474be,
    0x5e1c6893, 0x126bec01, 0x71f4d89c, 0x757548b4, 0x23390690, 0xf40f4cf7,
    0x4fcd3373, 0xf2172e98, 0xb9922aff, 0x646c3ab4, 0xd2ef343b, 0x9d38c1e6,
    0x3cd37001, 0xd79b26cf, 0x1f568d39, 0x7c6d6355, 0xc4ca637f, 0xaa3a80e6,
    0x9be8c94a, 0x260b53f8, 0xa42683bf, 0xa7b9f22a, 0xb134f326, 0xe9c72416,
    0xd1614a35, 0x937fc772, 0x7f87f200, 0x952b6b29, 0x616f909f, 0x6b527aa8,
    0xdc2d31d3, 0xce14cc6a, 0xb10366b2, 0x76efd23a, 0x39b15683, 0xa6de0de4,
    0x6896b3c1, 0x31cd66b7, 0xab7a2f62, 0xd754cdcd, 0xf40df9c9, 0xf9707edc,
    0xfa91d1bb, 0xccc8a8a5, 0x61003a17, 0xb4fcb461, 0x72a6681c, 0xe35bd382,
    0x2480a6d2, 0x4f4131e5, 0x19738cf0, 0x95485ec8, 0x14ef579f, 0x49d111c5,
    0x975610a1, 0x51ddcf78, 0xe68ab983, 0x10cd6f5f, 0xe0ae465c, 0x56f87907,
    0x3b5c12dc, 0x50e3633c, 0x879ad30b, 0xd76bb6b0, 0xd014e042, 0x96dedd7a,
    0x4e1eea8d, 0xe6079e4e, 0xc6944035, 0xc866e7a3, 0xf3ac825c, 0x43187fba,
    0xb3b1a633, 0x5589f5de, 0x6a29d58e, 0x35c88cba, 0x160094d5, 0xb0d207eb,
    0xfda6ea44, 0x099b3916, 0x7f4a7947, 0xc0353728, 0x5dada9bf, 0xcd329037,
    0xb2b0fad2, 0xbd79e8e9, 0x5eeb9be8, 0x726ffb2f, 0x61048c24, 0x9fd06d5a,
    0xb486cfe3, 0x94373606, 0x4b482744, 0xe068b60b, 0x52e3420d, 0x018ab9c1,
    0x54abfd10, 0x5e9fd4a8, 0x891be3ff, 0x3c4b951e, 0x215d8a09, 0xf7138508,
    0xbe0e8c16, 0x03bc6f4d, 0x4cc8c343, 0xd88f6a5f, 0xa0df643b, 0x8825086b,
    0xd991ae07, 0x7eaeda97, 0x4fd1b8d5, 0xf494fc5d, 0x08474fcd, 0x898e550a,
    0xd6c55513, 0x251abfaa,

};

/**
 * Helper function to run the RSA-4096 signing routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_sign`
 * using the constant test private key.
 *
 * @param msg Message to sign.
 * @param msg_len Message length in bytes.
 * @param padding_mode RSA padding mode.
 * @param hash_mode Hash function to use.
 * @param[out] sig Buffer for the generated RSA signature (4096 bits).
 * @return OK or error.
 */
static status_t run_rsa_4096_sign(const uint8_t *msg, size_t msg_len,
                                  rsa_padding_t padding_mode,
                                  rsa_hash_t hash_mode, uint32_t *sig) {
  key_mode_t key_mode;
  switch (padding_mode) {
    case kRsaPaddingPkcs:
      key_mode = kKeyModeRsaSignPkcs;
      break;
    case kRsaPaddingPss:
      key_mode = kKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  crypto_key_config_t private_key_config = {
      .version = kCryptoLibVersion1,
      .key_mode = key_mode,
      .key_length = kRsa4096NumBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kSecurityLevelLow,
  };

  rsa_private_key_t private_key = {
      .n = {.key_mode = key_mode,
            .key_length = sizeof(kTestModulus),
            .key = kTestModulus,
            .checksum = 0},
      .d = {.config = private_key_config,
            .keyblob = kTestPrivateExponent,
            .keyblob_length = sizeof(kTestPrivateExponent),
            .checksum = 0},
  };

  private_key.n.checksum = integrity_unblinded_checksum(&private_key.n);
  private_key.d.checksum = integrity_blinded_checksum(&private_key.d);

  crypto_const_byte_buf_t msg_buf = {
      .data = msg,
      .len = msg_len,
  };

  crypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa4096NumWords,
  };

  return otcrypto_rsa_sign(&private_key, msg_buf, padding_mode, hash_mode,
                           &sig_buf);
}

/**
 * Helper function to run the RSA-4096 verification routine.
 *
 * Packages input into cryptolib-style structs and calls `otcrypto_rsa_verify`
 * using the constant test public key.
 *
 * @param msg Message to verify.
 * @param msg_len Message length in bytes.
 * @param sig Signature to verify
 * @param padding_mode RSA padding mode.
 * @param hash_mode Hash function to use.
 * @param[out] verification_result Whether the signature passed verification.
 * @return OK or error.
 */
static status_t run_rsa_4096_verify(const uint8_t *msg, size_t msg_len,
                                    const uint32_t *sig,
                                    const rsa_padding_t padding_mode,
                                    const rsa_hash_t hash_mode,
                                    hardened_bool_t *verification_result) {
  key_mode_t key_mode;
  switch (padding_mode) {
    case kRsaPaddingPkcs:
      key_mode = kKeyModeRsaSignPkcs;
      break;
    case kRsaPaddingPss:
      key_mode = kKeyModeRsaSignPss;
      break;
    default:
      return INVALID_ARGUMENT();
  };

  rsa_public_key_t public_key = {
      .n = {.key_mode = key_mode,
            .key_length = sizeof(kTestModulus),
            .key = kTestModulus,
            .checksum = 0},
      .e = {.key_mode = key_mode,
            .key_length = sizeof(kTestPublicExponent),
            .key = &kTestPublicExponent,
            .checksum = 0},
  };

  public_key.n.checksum = integrity_unblinded_checksum(&public_key.n);
  public_key.e.checksum = integrity_unblinded_checksum(&public_key.e);

  crypto_const_byte_buf_t msg_buf = {
      .data = msg,
      .len = msg_len,
  };

  crypto_const_word32_buf_t sig_buf = {
      .data = sig,
      .len = kRsa4096NumWords,
  };

  return otcrypto_rsa_verify(&public_key, msg_buf, padding_mode, hash_mode,
                             sig_buf, verification_result);
}

status_t pkcs1v15_sign_test(void) {
  // Generate a signature using PKCS#1 v1.5 padding and SHA-512 as the hash
  // function.
  uint32_t sig[kRsa4096NumWords];
  TRY(run_rsa_4096_sign(kTestMessage, kTestMessageLen, kRsaPaddingPkcs,
                        kRsaHashSha512, sig));

  // Compare to the expected signature.
  TRY_CHECK_ARRAYS_EQ(sig, kValidSignaturePkcs1v15,
                      ARRAYSIZE(kValidSignaturePkcs1v15));
  return OK_STATUS();
}

status_t pkcs1v15_verify_valid_test(void) {
  // Try to verify a valid signature.
  hardened_bool_t verification_result;
  TRY(run_rsa_4096_verify(kTestMessage, kTestMessageLen,
                          kValidSignaturePkcs1v15, kRsaPaddingPkcs,
                          kRsaHashSha512, &verification_result));

  // Expect the signature to pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
}

status_t pkcs1v15_verify_invalid_test(void) {
  // Try to verify an invalid signature (wrong padding mode).
  hardened_bool_t verification_result;
  TRY(run_rsa_4096_verify(kTestMessage, kTestMessageLen, kValidSignaturePss,
                          kRsaPaddingPkcs, kRsaHashSha512,
                          &verification_result));

  // Expect the signature to fail verification.
  TRY_CHECK(verification_result == kHardenedBoolFalse);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

// Holds the test result.
static volatile status_t test_result;

bool test_main(void) {
  test_result = OK_STATUS();
  EXECUTE_TEST(test_result, pkcs1v15_sign_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_valid_test);
  EXECUTE_TEST(test_result, pkcs1v15_verify_invalid_test);
  return status_ok(test_result);
}
