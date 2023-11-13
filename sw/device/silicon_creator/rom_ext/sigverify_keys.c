// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"

/**
 * Determines whether a key is valid.
 *
 * Only key_types with known enumerated values are valid.
 *
 * @param key_type Type of the key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t key_is_valid(sigverify_key_type_t key_type) {
  switch (launder32(key_type)) {
    case kSigverifyKeyTypeFirmwareTest:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeFirmwareTest);
      return kErrorOk;
    case kSigverifyKeyTypeFirmwareProd:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeFirmwareProd);
      return kErrorOk;
    case kSigverifyKeyTypeFirmwareDev:
      HARDENED_CHECK_EQ(key_type, kSigverifyKeyTypeFirmwareDev);
      return kErrorOk;
    default:
      HARDENED_TRAP();
      OT_UNREACHABLE();
  }
}

rom_error_t sigverify_rsa_key_get(uint32_t key_id,
                                  const sigverify_rsa_key_t **key) {
  size_t cand_key_index = UINT32_MAX;
  // Random start index that is less than `kSigverifyRsaKeysCnt`.
  size_t i = ((uint64_t)rnd_uint32() * (uint64_t)kSigverifyRsaKeysCnt) >> 32;
  size_t iter_cnt = 0;
  for (; launder32(iter_cnt) < kSigverifyRsaKeysCnt; ++iter_cnt) {
    const sigverify_rom_ext_key_t *k = &kSigverifyRsaKeys[i];
    size_t k_id = sigverify_rsa_key_id_get(&k->key.n);
    if (launder32(k_id) == key_id) {
      HARDENED_CHECK_EQ(k_id, key_id);
      cand_key_index = i;
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
    rom_error_t error =
        key_is_valid(kSigverifyRsaKeys[cand_key_index].key_type);
    HARDENED_CHECK_EQ(error, kErrorOk);
    *key = &kSigverifyRsaKeys[cand_key_index].key;
    return error;
  }

  return kErrorSigverifyBadKey;
}
