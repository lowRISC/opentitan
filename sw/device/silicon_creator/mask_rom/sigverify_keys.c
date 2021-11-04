// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/mask_rom/keys/test_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/mask_rom/keys/test_key_1_rsa_3072_exp_3.h"
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
    [1] =
        {
            .key = TEST_KEY_1_RSA_3072_EXP_3,
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
  if (bitfield_field32_read(otp_read32(addr), field) == kHardenedByteBoolTrue) {
    return kErrorOk;
  }
  return kErrorSigverifyBadKey;
}

/**
 * Determines whether a test key is valid in the given life cycle state.
 *
 * A test key is valid if the device is in:
 *  - A TEST_UNLOCKED state or
 *  - The RMA state and the key is valid in OTP.
 *
 * @param lc_state Life cycle state of the device.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t test_key_is_valid(lifecycle_state_t lc_state,
                                     size_t key_index) {
  switch (lc_state) {
    case kLcStateTestUnlocked0:
    case kLcStateTestUnlocked1:
    case kLcStateTestUnlocked2:
    case kLcStateTestUnlocked3:
    case kLcStateTestUnlocked4:
    case kLcStateTestUnlocked5:
    case kLcStateTestUnlocked6:
    case kLcStateTestUnlocked7:
      // We don't read from OTP since it may not be programmed yet.
      return kErrorOk;
    case kLcStateRma:
      return key_is_valid_in_otp(key_index);
    default:
      return kErrorSigverifyBadKey;
  }
}

/**
 * Determines whether a production key is valid in the given life cycle state.
 *
 * A production is key is valid if the device is in:
 *  - A TEST_UNLOCKED state, or
 *  - An operational state (PROD, PROD_END, DEV, or RMA) and the key is valid in
 * OTP.
 *
 * @param lc_state Life cycle state of the device.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t prod_key_is_valid(lifecycle_state_t lc_state,
                                     size_t key_index) {
  switch (lc_state) {
    case kLcStateTestUnlocked0:
    case kLcStateTestUnlocked1:
    case kLcStateTestUnlocked2:
    case kLcStateTestUnlocked3:
    case kLcStateTestUnlocked4:
    case kLcStateTestUnlocked5:
    case kLcStateTestUnlocked6:
    case kLcStateTestUnlocked7:
      // We don't read from OTP since it may not be programmed yet.
      return kErrorOk;
    case kLcStateProd:
    case kLcStateProdEnd:
    case kLcStateDev:
    case kLcStateRma:
      return key_is_valid_in_otp(key_index);
    default:
      return kErrorSigverifyBadKey;
  }
}

/**
 * Determines whether a development key is valid in the given life cycle state.
 *
 * A development key is valid only if the device is in the DEV state and the key
 * is valid in OTP.
 *
 * @param lc_state Life cycle state of the device.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
static rom_error_t dev_key_is_valid(lifecycle_state_t lc_state,
                                    size_t key_index) {
  if (lc_state == kLcStateDev) {
    return key_is_valid_in_otp(key_index);
  }
  return kErrorSigverifyBadKey;
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
  switch (key_type) {
    case kSigverifyKeyTypeTest:
      return test_key_is_valid(lc_state, key_index);
    case kSigverifyKeyTypeProd:
      return prod_key_is_valid(lc_state, key_index);
    case kSigverifyKeyTypeDev:
      return dev_key_is_valid(lc_state, key_index);
    default:
      return kErrorSigverifyBadKey;
  }
}

rom_error_t sigverify_rsa_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_rsa_key_t **key) {
  const sigverify_mask_rom_key_t *keys = sigverify_rsa_keys_ptr_get();
  size_t num_keys = sigverify_num_rsa_keys_get();
  for (size_t i = 0; i < num_keys; ++i) {
    const sigverify_mask_rom_key_t *cand_key = &keys[i];
    if (sigverify_rsa_key_id_get(&cand_key->key.n) == key_id) {
      RETURN_IF_ERROR(key_is_valid(cand_key->key_type, lc_state, i));
      *key = &cand_key->key;
      return kErrorOk;
    }
  }
  return kErrorSigverifyBadKey;
}

extern const sigverify_mask_rom_key_t *sigverify_rsa_keys_ptr_get(void);
extern size_t sigverify_num_rsa_keys_get(void);
