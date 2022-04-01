// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/mask_rom/keys/test_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys_ptrs.h"

#include "otp_ctrl_regs.h"

/**
 * Public keys for signature verification.
 *
 * Please see sw/device/silicon_creator/mask_rom/keys/README.md for more
 * details.
 */
const sigverify_mask_rom_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys] = {
    [0] =
        {
            .key = TEST_KEY_0_RSA_3072_EXP_F4,
            .key_type = kSigverifyKeyTypeTest,
        },
};

static_assert(OTP_CTRL_PARAM_CREATOR_SW_CFG_KEY_IS_VALID_SIZE >=
                  kSigVerifyNumRsaKeys,
              "CREATOR_SW_CFG_KEY_IS_VALID OTP item must be at least "
              "`kSigVerifyNumRsaKeys` bytes.");

/**
 * Checks the validity of a key in OTP.
 *
 * Validity of each public key is encoded using a byte-sized
 * `hardened_byte_bool_t` in the `CREATOR_SW_CFG_KEY_IS_VALID` OTP item.
 *
 * @param key_index Index of the key to check.
 * @return Whether the key is valid or not.
 */
static rom_error_t key_is_valid_in_otp(size_t key_index) {
  const uint32_t addr =
      OTP_CTRL_PARAM_CREATOR_SW_CFG_KEY_IS_VALID_OFFSET +
      (key_index / kSigverifyNumEntriesPerOtpWord) * sizeof(uint32_t);
  const bitfield_field32_t field = {
      .mask = UINT8_MAX,
      .index = (key_index % kSigverifyNumEntriesPerOtpWord) * 8,
  };
  hardened_byte_bool_t is_valid =
      bitfield_field32_read(otp_read32(addr), field);
  if (launder32(is_valid) == kHardenedByteBoolTrue) {
    HARDENED_CHECK_EQ(is_valid, kHardenedByteBoolTrue);
    return kErrorOk;
  }
  return kErrorSigverifyBadKey;
}

/**
 * Determines whether a key is valid in the RMA life cycle state.
 *
 * Only test and production keys that are not invalidated in OTP are valid in
 * the RMA life cycle state.
 *
 * @param key_type Type of the key.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t key_is_valid_in_lc_state_rma(sigverify_key_type_t key_type,
                                                size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return key_is_valid_in_otp(key_index);
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(key_index);
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorSigverifyBadKey;
    default:
      HARDENED_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in the DEV life cycle state.
 *
 * Only production and development keys that are not invalidated in OTP are
 * valid in the DEV life cycle state.
 *
 * @param key_type Type of the key.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t key_is_valid_in_lc_state_dev(sigverify_key_type_t key_type,
                                                size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(key_index);
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return key_is_valid_in_otp(key_index);
    default:
      HARDENED_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in PROD and PROD_END life cycle states.
 *
 * Only production keys that are not invalidated in OTP are valid in PROD and
 * PROD_END life cycle states.
 *
 * @param key_type Type of the key.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t key_is_valid_in_lc_state_prod(sigverify_key_type_t key_type,
                                                 size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(key_index);
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return kErrorSigverifyBadKey;
    default:
      HARDENED_UNREACHABLE();
  }
}

/**
 * Determines whether a key is valid in TEST_UNLOCKED_* life cycle states.
 *
 * Only test and production keys are valid in TEST_UNLOCKED_* states. We don't
 * read from OTP since it may not be programmed yet.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
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
      HARDENED_UNREACHABLE();
  }
}

/**
 * Determines whether a given key is valid in the given life cycle state.
 *
 * @param key_type Type of the key.
 * @param lc_state Life cycle state of the device.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t key_is_valid(sigverify_key_type_t key_type,
                                lifecycle_state_t lc_state, size_t key_index) {
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return key_is_valid_in_lc_state_test(key_type);
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      return key_is_valid_in_lc_state_prod(key_type, key_index);
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      return key_is_valid_in_lc_state_prod(key_type, key_index);
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      return key_is_valid_in_lc_state_dev(key_type, key_index);
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return key_is_valid_in_lc_state_rma(key_type, key_index);
    default:
      HARDENED_UNREACHABLE();
  }
}

rom_error_t sigverify_rsa_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_rsa_key_t **key) {
  const sigverify_mask_rom_key_t *keys = sigverify_rsa_keys_ptr_get();
  size_t num_keys = sigverify_num_rsa_keys_get();
  size_t step = sigverify_rsa_keys_step_get();
  size_t cand_key_index = UINT32_MAX;
  // Random start index that is less than `num_keys`.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)num_keys) >> 32;
  size_t iter_cnt = 0;
  for (; launder32(iter_cnt) < num_keys; ++iter_cnt) {
    const sigverify_mask_rom_key_t *k = &keys[i];
    size_t k_id = sigverify_rsa_key_id_get(&k->key.n);
    if (launder32(k_id) == key_id) {
      HARDENED_CHECK_EQ(k_id, key_id);
      rom_error_t error = key_is_valid(k->key_type, lc_state, i);
      if (launder32(error) == kErrorOk) {
        HARDENED_CHECK_EQ(error, kErrorOk);
        cand_key_index = i;
      }
    }
    i += step;
    if (launder32(i) >= num_keys) {
      i -= num_keys;
    }
    HARDENED_CHECK_LT(i, num_keys);
  }
  HARDENED_CHECK_EQ(iter_cnt, num_keys);

  if (launder32(cand_key_index) < num_keys) {
    HARDENED_CHECK_LT(cand_key_index, num_keys);
    rom_error_t error =
        key_is_valid(keys[cand_key_index].key_type, lc_state, cand_key_index);
    HARDENED_CHECK_EQ(error, kErrorOk);
    *key = &keys[cand_key_index].key;
    return error;
  }

  return kErrorSigverifyBadKey;
}

extern const sigverify_mask_rom_key_t *sigverify_rsa_keys_ptr_get(void);
extern size_t sigverify_num_rsa_keys_get(void);
extern size_t sigverify_rsa_keys_step_get(void);
