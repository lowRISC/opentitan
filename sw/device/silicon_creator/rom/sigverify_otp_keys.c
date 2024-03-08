// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/lib/sw/device/silicon_creator/error.h"

#include "otp_ctrl_regs.h"

enum {
  // The size of the `ROT_CREATOR_AUTH_CODESIGN` partition ignoring the size of
  // the partition digest.
  kAuthCodesignParitionSize =
      OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_SIZE -
      OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_DIGEST_SIZE,

  // The size of the `ROT_CREATOR_AUTH_CODESIGN` region used to store the key
  // material. This is the size of the partition minus the size of the HMAC
  // digest used to measure the integrity of the keys.
  kAuthcodesignPartitionMsgSize =
      kAuthCodesignParitionSize - sizeof(hmac_digest_t),

  // The size of the `ROT_CREATOR_AUTH_STATE` partition ignoring the size of the
  // partition digest.
  kAuthStatePartitionSize = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_SIZE -
                            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_DIGEST_SIZE,
};

static_assert(sizeof(sigverify_otp_keys_t) == kAuthCodesignParitionSize,
              "Size of sigverify_otp_keys_t must match the size of the OTP "
              "partition");
static_assert(
    sizeof(sigverify_otp_key_states_t) == kAuthStatePartitionSize,
    "Size of sigverify_otp_key_states_t must match the size of the OTP "
    "partition");

/**
 * Determines whether a key is valid in the RMA life cycle state.
 *
 * Only test and production keys that are valid in the RMA life cycle state.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_rma(sigverify_key_type_t key_type) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorOk;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return kErrorOk;
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorSigverifyBadKey;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in the DEV life cycle state.
 *
 * Only production and development keys are valid in the DEV life cycle state.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_dev(sigverify_key_type_t key_type) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return kErrorOk;
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorOk;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in PROD and PROD_END life cycle states.
 *
 * Only production keys are valid in PROD and PROD_END life cycle states.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_prod(
    sigverify_key_type_t key_type) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return kErrorOk;
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorSigverifyBadKey;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in TEST_UNLOCKED_* life cycle states.
 *
 * Only test and production keys are valid in TEST_UNLOCKED_* states.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_test(
    sigverify_key_type_t key_type) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorOk;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return kErrorOk;
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorSigverifyBadKey;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

/**
 * Determines whether a given key is valid in the given life cycle state.
 *
 * @param key_type Type of the key.
 * @param lc_state Life cycle state of the device.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid(sigverify_key_type_t key_type,
                                lifecycle_state_t lc_state) {
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return key_is_valid_in_lc_state_test(key_type);
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      return key_is_valid_in_lc_state_prod(key_type);
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      return key_is_valid_in_lc_state_prod(key_type);
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      return key_is_valid_in_lc_state_dev(key_type);
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return key_is_valid_in_lc_state_rma(key_type);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t sigverify_otp_keys_init(sigverify_otp_key_ctx_t *ctx) {
  uint32_t *raw_buffer = (uint32_t *)&ctx->keys;
  size_t i;
  for (i = 0; launder32(i) < kAuthCodesignParitionSize; ++i) {
    raw_buffer[i] = otp_read32(OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_OFFSET +
                               i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, kAuthCodesignParitionSize);

  uint32_t *raw_state = (uint32_t *)&ctx->states;
  for (i = 0; launder32(i) < kAuthStatePartitionSize; ++i) {
    raw_state[i] = otp_read32(OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_OFFSET +
                              i * sizeof(uint32_t));
  }
  HARDENED_CHECK_EQ(i, kAuthStatePartitionSize);
  return sigverify_otp_keys_check(ctx);
}

rom_error_t sigverify_otp_keys_check(sigverify_otp_key_ctx_t *ctx) {
  hmac_digest_t got;
  hmac_sha256(&ctx->keys, kAuthcodesignPartitionMsgSize, &got);
  size_t i = 0;
  for (; launder32(i) < kHmacDigestNumWords; ++i) {
    if (got.digest[i] != ctx->keys.integrity_measurement.digest[i]) {
      return kErrorSigverifyBadAuthPartition;
    }
  }
  HARDENED_CHECK_EQ(i, kHmacDigestNumWords);
  return kErrorOk;
}

/**
 * Utility function to get a key entry from any array.
 *
 * @param array An array.
 * @param entry_size Size of each entry in `array`.
 * @param entry_index Index of the entry to get.
 * @return Requested entry.
 */
OT_WARN_UNUSED_RESULT
static inline const sigverify_rom_key_header_t *array_get_generic(
    const sigverify_rom_key_header_t *array, size_t entry_size,
    size_t entry_index) {
  return (const sigverify_rom_key_header_t *)((const char *)array +
                                              entry_size * entry_index);
}

rom_error_t sigverify_otp_keys_get(sigverify_otp_keys_get_params_t params,
                                   const sigverify_rom_key_header_t **key) {
  size_t cand_key_index = UINT32_MAX;

  // Randomize the start index to avoid always picking the first key. A
  // potential attacker will have a hardtime predicting the timing in which the
  // key will be selected.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)params.key_cnt) >> 32;

  // Use forward and backwards iteration counters to ensure that the loop was
  // executed exactly `params.key_cnt` times. This is to prevent faults causing
  // the loop to skip inner iterations.
  size_t iter_cnt = 0, r_iter_cnt = params.key_cnt - 1;
  for (; launder32(iter_cnt) < params.key_cnt &&
         launder32(r_iter_cnt) < params.key_cnt;
       ++iter_cnt, --r_iter_cnt) {
    const sigverify_rom_key_header_t *k =
        array_get_generic(params.key_array, params.key_size, i);
    if (k->key_id == params.key_id) {
      HARDENED_CHECK_EQ(k->key_id, params.key_id);
      if (params.key_states[i] == kSigVerifyKeyAuthStateEnabled) {
        rom_error_t error = key_is_valid(k->key_type, params.lc_state);
        if (launder32(error) == kErrorOk) {
          HARDENED_CHECK_EQ(error, kErrorOk);
          // Store the index of the valid key rather than returning early. This
          // is to make it harder for an attacker to predict the timing of the
          // function. This will also allow us to perform a redundant check to
          // ensure that the key is valid.
          cand_key_index = i;
        }
      }
      i++;
      if (launder32(i) >= params.key_cnt) {
        i -= params.key_cnt;
      }
      HARDENED_CHECK_LT(i, params.key_cnt);
    }
  }
  // Ensure that the loop was executed exactly `params.key_cnt` times.
  HARDENED_CHECK_EQ(iter_cnt, params.key_cnt);
  HARDENED_CHECK_EQ((uint32_t)r_iter_cnt, UINT32_MAX);

  // Verify the key a second time and only return it if it passes all checks.
  // The hardened check macros create barriers in the code, causing the binary
  // to perform the checks as written in the code (i.e. the checks, or their
  // order, cannot be optimized out by the compiler). This is a security measure
  // to ensure that the checks are performed as intended.
  if (launder32(cand_key_index) < params.key_cnt) {
    HARDENED_CHECK_LT(cand_key_index, params.key_cnt);
    const sigverify_rom_key_header_t *cand_key =
        array_get_generic(params.key_array, params.key_size, cand_key_index);
    if (params.key_states[cand_key_index] == kSigVerifyKeyAuthStateEnabled) {
      rom_error_t error = key_is_valid(cand_key->key_type, params.lc_state);
      HARDENED_CHECK_EQ(error, kErrorOk);
      *key = cand_key;
      return error;
    }
  }
  return kErrorSigverifyBadKey;
}
