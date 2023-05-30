// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_rsa.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"

/**
 * Checks the validity of a key in OTP.
 *
 * Validity of each public key is encoded using a byte-sized
 * `hardened_byte_bool_t` in the `CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN` OTP item.
 *
 * @param key_index Index of the key to check.
 * @return Whether the key is valid or not.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_otp(size_t otp_offset, size_t key_index) {
  const uint32_t addr =
      otp_offset +
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
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_rma(sigverify_key_type_t key_type,
                                                size_t otp_offset,
                                                size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return key_is_valid_in_otp(otp_offset, key_index);
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(otp_offset, key_index);
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
 * Only production and development keys that are not invalidated in OTP are
 * valid in the DEV life cycle state.
 *
 * @param key_type Type of the key.
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_dev(sigverify_key_type_t key_type,
                                                size_t otp_offset,
                                                size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(otp_offset, key_index);
    case kSigverifyKeyTypeDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeDev);
      return key_is_valid_in_otp(otp_offset, key_index);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
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
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid_in_lc_state_prod(sigverify_key_type_t key_type,
                                                 size_t otp_offset,
                                                 size_t key_index) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeTest);
      return kErrorSigverifyBadKey;
    case kSigverifyKeyTypeProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeProd);
      return key_is_valid_in_otp(otp_offset, key_index);
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
 * Only test and production keys are valid in TEST_UNLOCKED_* states. We don't
 * read from OTP since it may not be programmed yet.
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
 * @param key_index Index of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid(sigverify_key_type_t key_type,
                                lifecycle_state_t lc_state, size_t otp_offset,
                                size_t key_index) {
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return key_is_valid_in_lc_state_test(key_type);
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      return key_is_valid_in_lc_state_prod(key_type, otp_offset, key_index);
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      return key_is_valid_in_lc_state_prod(key_type, otp_offset, key_index);
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      return key_is_valid_in_lc_state_dev(key_type, otp_offset, key_index);
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return key_is_valid_in_lc_state_rma(key_type, otp_offset, key_index);
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
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

rom_error_t sigverify_key_get(sigverify_key_get_in_params_t in_params,
                              const sigverify_rom_key_header_t **key) {
  size_t cand_key_index = UINT32_MAX;
  // Random start index that is less than `in_params.key_cnt`.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)in_params.key_cnt) >> 32;
  size_t iter_cnt = 0, r_iter_cnt = in_params.key_cnt - 1;
  for (; launder32(iter_cnt) < in_params.key_cnt &&
         launder32(r_iter_cnt) < in_params.key_cnt;
       ++iter_cnt, --r_iter_cnt) {
    const sigverify_rom_key_header_t *k =
        array_get_generic(in_params.key_array, in_params.key_size, i);
    if (launder32(sigverify_rom_key_id_get(k)) == in_params.key_id) {
      HARDENED_CHECK_EQ(sigverify_rom_key_id_get(k), in_params.key_id);
      rom_error_t error = key_is_valid(k->key_type, in_params.lc_state,
                                       in_params.otp_offset, i);
      if (launder32(error) == kErrorOk) {
        HARDENED_CHECK_EQ(error, kErrorOk);
        cand_key_index = i;
      }
    }
    i += in_params.step;
    if (launder32(i) >= in_params.key_cnt) {
      i -= in_params.key_cnt;
    }
    HARDENED_CHECK_LT(i, in_params.key_cnt);
  }
  HARDENED_CHECK_EQ(iter_cnt, in_params.key_cnt);
  HARDENED_CHECK_EQ((uint32_t)r_iter_cnt, UINT32_MAX);

  if (launder32(cand_key_index) < in_params.key_cnt) {
    HARDENED_CHECK_LT(cand_key_index, in_params.key_cnt);
    const sigverify_rom_key_header_t *cand_key = array_get_generic(
        in_params.key_array, in_params.key_size, cand_key_index);
    rom_error_t error = key_is_valid(cand_key->key_type, in_params.lc_state,
                                     in_params.otp_offset, cand_key_index);
    HARDENED_CHECK_EQ(error, kErrorOk);
    *key = cand_key;
    return error;
  }

  return kErrorSigverifyBadKey;
}

// Extern declarations for the inline functions in the header.
extern uint32_t sigverify_rom_key_id_get(const sigverify_rom_key_header_t *key);
