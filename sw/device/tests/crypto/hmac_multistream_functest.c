// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "hmac_testvectors.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 's', 't')

// We need the following assertion, because we are using hash context struct
// also for hmac contexts.
static_assert(sizeof(otcrypto_hash_context_t) ==
                  sizeof(otcrypto_hmac_context_t),
              "Hash and Hmac contexts are expected to be of the same length");

/**
 * Determines `hash_mode` for given SHA-2 test vectors.
 *
 * Note that for HMAC operations, mode information is part of the key struct,
 * hence this function is only used for hash vectors.
 *
 * @param test_vec The pointer to the test vector.
 * @param[out] hash_mode The determined hash_mode of the given test vector.
 */
static status_t get_hash_mode(hmac_test_vector_t *test_vec,
                              otcrypto_hash_mode_t *hash_mode) {
  switch (test_vec->test_operation) {
    case kHmacTestOperationSha256:
      *hash_mode = kOtcryptoHashModeSha256;
      return OTCRYPTO_OK;
    case kHmacTestOperationSha384:
      *hash_mode = kOtcryptoHashModeSha384;
      return OTCRYPTO_OK;
    case kHmacTestOperationSha512:
      *hash_mode = kOtcryptoHashModeSha512;
      return OTCRYPTO_OK;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}

/**
 * Instantiate `hash_ctx` context object with hash/mac mode specified in
 * `current_test_vector`.
 *
 * @param hash_ctx Corresponding context for given `current_test_vector`.
 * @param current_test_vector Pointer to the hardcoded test vector.
 */
static status_t ctx_init(otcrypto_hash_context_t *hash_ctx,
                         hmac_test_vector_t *current_test_vector) {
  // Populate `checksum` and `config.security_level` fields.
  current_test_vector->key.checksum =
      integrity_blinded_checksum(&current_test_vector->key);

  otcrypto_hash_mode_t hash_mode;

  switch (current_test_vector->test_operation) {
    case kHmacTestOperationSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha512:
      LOG_INFO("Invoking hash_init for %s.",
               current_test_vector->vector_identifier);
      TRY(get_hash_mode(current_test_vector, &hash_mode));
      TRY(otcrypto_hash_init(hash_ctx, hash_mode));
      break;
    case kHmacTestOperationHmacSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha512:
      LOG_INFO("Invoking hmac_init for %s.",
               current_test_vector->vector_identifier);
      TRY(otcrypto_hmac_init((otcrypto_hmac_context_t *)hash_ctx,
                             &current_test_vector->key));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Feed messages to the streaming hash/hmac operation with context `hash_ctx`.
 * `current_test_vector` is used to determine message bytes to be used.
 *
 * This function feeds (approximately) the first or the second half of
 * `current_test_vector->message`.
 *
 * @param hash_ctx Corresponding context for given `current_test_vector`.
 * @param current_test_vector Pointer to the hardcoded test vector.
 * @param segment_index Determines whether the first or the second half of the
 * message to be used to update the context.
 */
static status_t feed_msg(otcrypto_hash_context_t *hash_ctx,
                         hmac_test_vector_t *current_test_vector,
                         size_t segment_index) {
  size_t segment_start;
  size_t segment_length;
  if (segment_index == 0) {
    segment_start = 0;
    segment_length = current_test_vector->message.len / 2;
  } else if (segment_index == 1) {
    segment_start = current_test_vector->message.len / 2;
    segment_length =
        current_test_vector->message.len - current_test_vector->message.len / 2;
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  otcrypto_const_byte_buf_t msg = {
      .data = &current_test_vector->message.data[segment_start],
      .len = segment_length,
  };
  LOG_INFO("Feeding message part %d for %s.", segment_index,
           current_test_vector->vector_identifier);
  switch (current_test_vector->test_operation) {
    case kHmacTestOperationSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha512:
      TRY(otcrypto_hash_update(hash_ctx, msg));
      break;
    case kHmacTestOperationHmacSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha512:
      TRY(otcrypto_hmac_update((otcrypto_hmac_context_t *)hash_ctx, msg));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Finalize the hash/hmac operation with context `hash_ctx`. Further necessary
 * parameters for the final call is reads from `current_test_vector`.
 *
 * @param hash_ctx Corresponding context for given `current_test_vector`.
 * @param current_test_vector Pointer to the hardcoded test vector.
 */
static status_t hmac_finalize(otcrypto_hash_context_t *hash_ctx,
                              hmac_test_vector_t *current_test_vector) {
  // The test vectors already have the correct digest sizes hardcoded.
  size_t digest_len = current_test_vector->digest.len;
  // Allocate the buffer for the maximum digest size (which comes from SHA-512).
  uint32_t act_tag[kSha512DigestWords];
  otcrypto_word32_buf_t tag_buf = {
      .data = act_tag,
      .len = digest_len,
  };
  otcrypto_hash_digest_t hash_digest = {
      // .mode is to be determined below in switch-case block.
      .data = act_tag,
      .len = digest_len,
  };
  LOG_INFO("Invoking final call for %s.",
           current_test_vector->vector_identifier);
  switch (current_test_vector->test_operation) {
    case kHmacTestOperationSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationSha512:
      TRY(get_hash_mode(current_test_vector, &hash_digest.mode));
      TRY(otcrypto_hash_final(hash_ctx, hash_digest));
      break;
    case kHmacTestOperationHmacSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHmacTestOperationHmacSha512:
      TRY(otcrypto_hmac_final((otcrypto_hmac_context_t *)hash_ctx, tag_buf));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  LOG_INFO("Comparing result for %s.", current_test_vector->vector_identifier);
  TRY_CHECK_ARRAYS_EQ(act_tag, current_test_vector->digest.data, digest_len);
  return OTCRYPTO_OK;
}

/**
 * Run all vectors specified in `kHmacTestVectors` in parallel. Namely:
 * i) Each stream is instantiated (by init call).
 * ii) Each stream receives the first half its message.
 * iii) Each stream receives the second half of its message.
 * iv) Each stream is concluded with a final call and the digest result is
 * compared with the expected valud.
 */
static status_t run_test(void) {
  // hash_contexts are also used as hmac_contexts, since their size is equal.
  otcrypto_hash_context_t hash_contexts[ARRAYSIZE(kHmacTestVectors)];
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    TRY(ctx_init(&hash_contexts[i], &kHmacTestVectors[i]));
  }
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    TRY(feed_msg(&hash_contexts[i], &kHmacTestVectors[i], /*segment_index=*/0));
  }
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    TRY(feed_msg(&hash_contexts[i], &kHmacTestVectors[i], /*segment_index=*/1));
  }
  for (size_t i = 0; i < ARRAYSIZE(kHmacTestVectors); i++) {
    TRY(hmac_finalize(&hash_contexts[i], &kHmacTestVectors[i]));
  }
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib SHA-2/HMAC with parallel multiple streams.");
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, run_test);
  return status_ok(test_result);
}
