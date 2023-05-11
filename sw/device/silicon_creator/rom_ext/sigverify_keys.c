// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"

/**
 * Determines whether a key is valid in the RMA life cycle state.
 *
 * Only test and production keys that are valid in the RMA life cycle state.
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
 * Only production and development keys that are valid in the DEV life cycle
 * state.
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
 * Only production keys that are valid in PROD and PROD_END life cycle
 * states.
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
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t sigverify_rsa_key_get(uint32_t key_id, lifecycle_state_t lc_state,
                                  const sigverify_rsa_key_t **key) {
  size_t cand_key_index = UINT32_MAX;
  // Random start index that is less than `kSigverifyRsaKeysCnt`.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)kSigverifyRsaKeysCnt) >> 32;
  size_t iter_cnt = 0;
  for (; launder32(iter_cnt) < kSigverifyRsaKeysCnt; ++iter_cnt) {
    const sigverify_rom_key_t *k = &kSigverifyRsaKeys[i];
    size_t k_id = sigverify_rsa_key_id_get(&k->key.n);
    if (launder32(k_id) == key_id) {
      HARDENED_CHECK_EQ(k_id, key_id);
      rom_error_t error = key_is_valid(k->key_type, lc_state, i);
      if (launder32(error) == kErrorOk) {
        HARDENED_CHECK_EQ(error, kErrorOk);
        cand_key_index = i;
      }
    }
    i += kSigverifyRsaKeysStep;
    if (launder32(i) >= kSigverifyRsaKeysCnt) {
      i -= kSigverifyRsaKeysCnt;
    }
    HARDENED_CHECK_LT(i, kSigverifyRsaKeysCnt);
  }
  HARDENED_CHECK_EQ(iter_cnt, kSigverifyRsaKeysCnt);

  if (launder32(cand_key_index) < kSigverifyRsaKeysCnt) {
    HARDENED_CHECK_LT(cand_key_index, kSigverifyRsaKeysCnt);
    rom_error_t error = key_is_valid(kSigverifyRsaKeys[cand_key_index].key_type,
                                     lc_state, cand_key_index);
    HARDENED_CHECK_EQ(error, kErrorOk);
    *key = &kSigverifyRsaKeys[cand_key_index].key;
    return error;
  }

  return kErrorSigverifyBadKey;
}
