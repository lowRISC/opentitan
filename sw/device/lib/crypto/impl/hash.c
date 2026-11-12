// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/hash.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/sha1.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 's', 'h')

// Ensure that `otcrypto_hash_context_t` can hold a mode word plus either a
// SHA-2 or SHA-1 streaming context.
static_assert(sizeof(otcrypto_hash_context_t) >=
                  sizeof(uint32_t) + sizeof(otcrypto_sha2_context_t),
              "`otcrypto_hash_context_t` must hold a mode word plus "
              "`otcrypto_sha2_context_t`.");
static_assert(sizeof(otcrypto_hash_context_t) >=
                  sizeof(uint32_t) + sizeof(otcrypto_sha1_context_t),
              "`otcrypto_hash_context_t` must hold a mode word plus "
              "`otcrypto_sha1_context_t`.");

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
          .compute = NULL,
      };
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha1:
      *info = (hash_info_t){
          .mode = kOtcryptoHashModeSha1,
          .digest_wordlen = 160 / 32,
          .der_oid = kSha1DigestIdentifier,
          .der_oid_len = sizeof(kSha1DigestIdentifier),
          .compute = otcrypto_sha1,
      };
      return OTCRYPTO_OK;
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

status_t hash_message(otcrypto_hash_mode_t hash_mode,
                      const otcrypto_const_byte_buf_t *message,
                      uint32_t *digest_data, otcrypto_hash_digest_t *digest) {
  hash_info_t info;
  HARDENED_TRY(hash_info_get(hash_mode, &info));
  if (info.compute == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  digest->mode = hash_mode;
  digest->len = info.digest_wordlen;
  digest->data = digest_data;
  return info.compute(message, digest);
}

otcrypto_status_t otcrypto_hash_init(otcrypto_hash_context_t *ctx,
                                     otcrypto_hash_mode_t hash_mode) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      ctx->data[0] = (uint32_t)hash_mode;
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      return otcrypto_sha2_init(hash_mode, sha2_ctx);
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      ctx->data[0] = (uint32_t)kOtcryptoHashModeSha1;
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      return otcrypto_sha1_init(sha1_ctx);
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }
}

otcrypto_status_t otcrypto_hash_update(
    otcrypto_hash_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || input_message == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                                ? kTestHashSha256Bit
                                : kTestHashSha512Bit);
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      return otcrypto_sha2_update(sha2_ctx, input_message);
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      return otcrypto_sha1_update(sha1_ctx, input_message);
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }
}

otcrypto_status_t otcrypto_hash_final(otcrypto_hash_context_t *ctx,
                                      otcrypto_hash_digest_t *digest) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest == NULL || digest->data == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  status_t status = OTCRYPTO_BAD_ARGS;
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                                ? kTestHashSha256Bit
                                : kTestHashSha512Bit);
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      status = otcrypto_sha2_final(sha2_ctx, digest);
      break;
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      status = otcrypto_sha1_final(sha1_ctx, digest);
      break;
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }

  HARDENED_TRY(hardened_memshred(ctx->data, ARRAYSIZE(ctx->data)));
  return status;
}

status_t hash_context_final(otcrypto_hash_context_t *ctx, uint32_t *digest_data,
                            otcrypto_hash_digest_t *digest) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest_data == NULL || digest == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  hash_info_t info;
  HARDENED_TRY(hash_info_get(hash_mode, &info));
  digest->mode = hash_mode;
  digest->len = info.digest_wordlen;
  digest->data = digest_data;

  return otcrypto_hash_final(ctx, digest);
}
