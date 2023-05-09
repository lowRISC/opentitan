// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/hash_shake.c

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/utils.h"

enum {
  /**
   * Number of bits needed to represent the `tree` field.
   */
  kSpxTreeBits = kSpxTreeHeight * (kSpxD - 1),
  /**
   * Number of bytes needed to represent the `tree` field.
   */
  kSpxTreeBytes = (kSpxTreeBits + 7) / 8,
  /**
   * Number of bits needed to represent a leaf index.
   */
  kSpxLeafBits = kSpxTreeHeight,
  /**
   * Number of bytes needed to represent a leaf index.
   */
  kSpxLeafBytes = (kSpxLeafBits + 7) / 8,
  /**
   * Number of bytes needed for the message digest.
   */
  kSpxDigestBytes = kSpxForsMsgBytes + kSpxTreeBytes + kSpxLeafBytes,
  /**
   * Number of 32-bit words needed for the message digest.
   *
   * Rounded up if necessary.
   */
  kSpxDigestWords = (kSpxDigestBytes + sizeof(uint32_t) - 1) / sizeof(uint32_t),
};

static_assert(
    kSpxTreeBits <= 64,
    "For given height and depth, 64 bits cannot represent all subtrees.");
static_assert(
    kSpxLeafBits <= 32,
    "For the given height, 32 bits is not large enough for a leaf index.");

rom_error_t spx_hash_initialize(spx_ctx_t *ctx) {
  return kmac_shake256_configure();
}

rom_error_t spx_hash_message(const uint32_t *R, const uint32_t *pk,
                             const uint8_t *msg_prefix_1,
                             size_t msg_prefix_1_len,
                             const uint8_t *msg_prefix_2,
                             size_t msg_prefix_2_len, const uint8_t *msg,
                             size_t msg_len, uint8_t *digest, uint64_t *tree,
                             uint32_t *leaf_idx) {
  uint32_t buf[kSpxDigestWords] = {0};
  unsigned char *bufp = (unsigned char *)buf;

  HARDENED_RETURN_IF_ERROR(kmac_shake256_start());
  kmac_shake256_absorb_words(R, kSpxNWords);
  kmac_shake256_absorb_words(pk, kSpxPkWords);
  kmac_shake256_absorb(msg_prefix_1, msg_prefix_1_len);
  kmac_shake256_absorb(msg_prefix_2, msg_prefix_2_len);
  kmac_shake256_absorb(msg, msg_len);
  kmac_shake256_squeeze_start();
  HARDENED_RETURN_IF_ERROR(kmac_shake256_squeeze_end(buf, kSpxDigestWords));

  memcpy(digest, bufp, kSpxForsMsgBytes);
  bufp += kSpxForsMsgBytes;

  if (kSpxTreeBits == 0) {
    *tree = 0;
  } else {
    *tree = spx_utils_bytes_to_u64(bufp, kSpxTreeBytes);
    *tree &= (~(uint64_t)0) >> (64 - kSpxTreeBits);
    bufp += kSpxTreeBytes;
  }

  *leaf_idx = (uint32_t)spx_utils_bytes_to_u64(bufp, kSpxLeafBytes);
  *leaf_idx &= (~(uint32_t)0) >> (32 - kSpxLeafBits);

  return kErrorOk;
}
