// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/hash.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 's', 'h')

static const uint8_t kSha256DigestIdentifier[] = {
    0x20, 0x04, 0x00, 0x05, 0x01, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x31, 0x30,
};
static const uint8_t kSha384DigestIdentifier[] = {
    0x30, 0x04, 0x00, 0x05, 0x02, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x41, 0x30,
};
static const uint8_t kSha512DigestIdentifier[] = {
    0x40, 0x04, 0x00, 0x05, 0x03, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x51, 0x30,
};
static const uint8_t kSha3_224DigestIdentifier[] = {
    0x1c, 0x04, 0x00, 0x05, 0x07, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x2d, 0x30,
};
static const uint8_t kSha3_256DigestIdentifier[] = {
    0x20, 0x04, 0x00, 0x05, 0x08, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x31, 0x30,
};
static const uint8_t kSha3_384DigestIdentifier[] = {
    0x30, 0x04, 0x00, 0x05, 0x09, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x41, 0x30,
};
static const uint8_t kSha3_512DigestIdentifier[] = {
    0x40, 0x04, 0x00, 0x05, 0x0a, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x51, 0x30,
};

status_t hash_info_get(otcrypto_hash_mode_t hash_mode, hash_info_t *info) {
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha256,
          .digest_wordlen = 256 / 32,
          .der_oid = kSha256DigestIdentifier,
          .der_oid_len = sizeof(kSha256DigestIdentifier),
          .compute = otcrypto_sha2_256,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha384:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha384,
          .digest_wordlen = 384 / 32,
          .der_oid = kSha384DigestIdentifier,
          .der_oid_len = sizeof(kSha384DigestIdentifier),
          .compute = otcrypto_sha2_384,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha512:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha512,
          .digest_wordlen = 512 / 32,
          .der_oid = kSha512DigestIdentifier,
          .der_oid_len = sizeof(kSha512DigestIdentifier),
          .compute = otcrypto_sha2_512,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_224:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_224,
          .digest_wordlen = 224 / 32,
          .der_oid = kSha3_224DigestIdentifier,
          .der_oid_len = sizeof(kSha3_224DigestIdentifier),
          .compute = otcrypto_sha3_224,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_256,
          .digest_wordlen = 256 / 32,
          .der_oid = kSha3_256DigestIdentifier,
          .der_oid_len = sizeof(kSha3_256DigestIdentifier),
          .compute = otcrypto_sha3_256,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_384:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_384,
          .digest_wordlen = 384 / 32,
          .der_oid = kSha3_384DigestIdentifier,
          .der_oid_len = sizeof(kSha3_384DigestIdentifier),
          .compute = otcrypto_sha3_384,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_512:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_512,
          .digest_wordlen = 512 / 32,
          .der_oid = kSha3_512DigestIdentifier,
          .der_oid_len = sizeof(kSha3_512DigestIdentifier),
          .compute = otcrypto_sha3_512,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashXofModeShake128:
      *info = (hash_info_t){
          .mode = kOtcryptoHashXofModeShake128,
          .digest_wordlen = 256 / 32,
          .der_oid = NULL,
          .der_oid_len = 0,
          .compute = otcrypto_shake128,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashXofModeShake256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashXofModeShake256,
          .digest_wordlen = 512 / 32,
          .der_oid = NULL,
          .der_oid_len = 0,
          .compute = otcrypto_shake256,
      };
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}

status_t hash_message(otcrypto_hash_mode_t hash_mode,
                      const otcrypto_const_byte_buf_t *message,
                      uint32_t *digest_data, otcrypto_hash_digest_t *digest) {
  hash_info_t info;
  HARDENED_TRY(hash_info_get(hash_mode, &info));
  digest->mode = hash_mode;
  digest->len = info.digest_wordlen;
  digest->data = digest_data;
  return info.compute(message, digest);
}
