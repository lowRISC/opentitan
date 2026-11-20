// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/hash.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 's', 'h')

/**
 * Digest identifiers for different hash functions (little-endian).
 *
 * See Note 1 in RFC 8017.
 */
static const uint8_t kSha1DigestIdentifier[] = {
    0x14, 0x04, 0x00, 0x05, 0x1a, 0x02, 0x03, 0x0e,
    0x2b, 0x05, 0x06, 0x09, 0x30, 0x21, 0x30,
};
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
/*
 * SHA-3 digest identifiers adapted from the SHA-2 identifiers based on the
 * algorithm identifiers on
 * https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
 */
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
    case kOtcryptoHashModeNull:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeNull,
          .digest_wordlen = 0,
          .der_oid = kSha1DigestIdentifier,
          .der_oid_len = 0,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha1:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha1,
          .digest_wordlen = 160 / 32,
          .der_oid = kSha1DigestIdentifier,
          .der_oid_len = sizeof(kSha1DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha256,
          .digest_wordlen = 256 / 32,
          .der_oid = kSha256DigestIdentifier,
          .der_oid_len = sizeof(kSha256DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha384:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha384,
          .digest_wordlen = 384 / 32,
          .der_oid = kSha384DigestIdentifier,
          .der_oid_len = sizeof(kSha384DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha512:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha512,
          .digest_wordlen = 512 / 32,
          .der_oid = kSha512DigestIdentifier,
          .der_oid_len = sizeof(kSha512DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_224:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_224,
          .digest_wordlen = 224 / 32,
          .der_oid = kSha3_224DigestIdentifier,
          .der_oid_len = sizeof(kSha3_224DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_256,
          .digest_wordlen = 256 / 32,
          .der_oid = kSha3_256DigestIdentifier,
          .der_oid_len = sizeof(kSha3_256DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_384:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_384,
          .digest_wordlen = 384 / 32,
          .der_oid = kSha3_384DigestIdentifier,
          .der_oid_len = sizeof(kSha3_384DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_512:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha3_512,
          .digest_wordlen = 512 / 32,
          .der_oid = kSha3_512DigestIdentifier,
          .der_oid_len = sizeof(kSha3_512DigestIdentifier),
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashXofModeShake128:
      *info = (hash_info_t){
          .mode = kOtcryptoHashXofModeShake128,
          .digest_wordlen = 256 / 32,
          .der_oid = NULL,
          .der_oid_len = 0,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashXofModeShake256:
      *info = (hash_info_t){
          .mode = kOtcryptoHashXofModeShake256,
          .digest_wordlen = 512 / 32,
          .der_oid = NULL,
          .der_oid_len = 0,
      };
      return OTCRYPTO_OK;
    default:
      // Unsupported or unrecognized hash function.
      // COVERAGE (MISSING) We do not cover bad padding modes.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) This is unreachable and is coded in as a fault
  // countermeasure.
  return OTCRYPTO_FATAL_ERR;
}

status_t sha2_message(otcrypto_hash_mode_t hash_mode,
                      const otcrypto_const_byte_buf_t *message,
                      uint32_t *digest) {
  OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                            ? kTestHashSha256Bit
                            : kTestHashSha512Bit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message == NULL || digest == NULL ||
      (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_ctx_t ctx;
  otcrypto_hash_mode_t hash_mode_used = launder32(0);
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
      hmac_hash_sha256_init(&ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha256;
      break;
    case kOtcryptoHashModeSha384:
      hmac_hash_sha384_init(&ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha384;
      break;
    case kOtcryptoHashModeSha512:
      hmac_hash_sha512_init(&ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha512;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(hash_mode_used), hash_mode);

  status_t status = OTCRYPTO_OK;
  if (message->len > 0) {
    status = hmac_update(&ctx, message);
  }
  if (status_ok(status)) {
    otcrypto_word32_buf_t digest_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, digest, ctx.digest_wordlen);
    status = hmac_final(&ctx, &digest_buf);
  }
  if (!status_ok(status)) {
    hardened_memshred((uint32_t *)&ctx, sizeof(ctx) / sizeof(uint32_t));
  }
  return status;
}

status_t hash_message(otcrypto_hash_mode_t hash_mode,
                      const otcrypto_const_byte_buf_t *message,
                      uint32_t *digest_data, otcrypto_hash_digest_t *digest) {
  otcrypto_hash_context_t ctx;
  HARDENED_TRY(otcrypto_hash_init(&ctx, hash_mode));
  status_t status = otcrypto_hash_update(&ctx, message);
  if (!status_ok(status)) {
    hardened_memshred(ctx.data, ARRAYSIZE(ctx.data));
    return status;
  }
  return hash_context_final(&ctx, digest_data, digest);
}

status_t hash_context_final(otcrypto_hash_context_t *ctx, uint32_t *digest_data,
                            otcrypto_hash_digest_t *digest) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest_data == NULL || digest == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha1:
      digest->len = 160 / 32;
      break;
    case kOtcryptoHashModeSha256:
      digest->len = 256 / 32;
      break;
    case kOtcryptoHashModeSha384:
      digest->len = 384 / 32;
      break;
    case kOtcryptoHashModeSha512:
      digest->len = 512 / 32;
      break;
    default:
      digest->len = 0;
      break;
  }
  digest->mode = hash_mode;
  digest->data = digest_data;

  return otcrypto_hash_final(ctx, digest);
}
