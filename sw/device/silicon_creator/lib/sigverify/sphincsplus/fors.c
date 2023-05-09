// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/fors.h

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/fors.h"

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/utils.h"

/**
 * Get the leaf value from the FORS secret key.
 *
 * @param sk Input secret key (`kSpxN` bytes).
 * @param ctx Context object.
 * @param fors_leaf_addr Leaf address.
 * @param[out] leaf Resulting leaf (`kSpxNWords` words).
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t fors_sk_to_leaf(const uint32_t *sk, const spx_ctx_t *ctx,
                                   spx_addr_t *fors_leaf_addr, uint32_t *leaf) {
  return thash(sk, /*inblocks=*/1, ctx, fors_leaf_addr, leaf);
}

/**
 * Interprets m as `kSpxForsHeight`-bit unsigned integers.
 *
 * Assumes m contains at least kSpxForsHeight * kSpxForsTrees bits.
 * Assumes indices has space for kSpxForsTrees integers.
 *
 * @param m Input message.
 * @param[out] indices Buffer for indices.
 */
static void message_to_indices(const uint8_t *m, uint32_t *indices) {
  size_t offset = 0;
  for (size_t i = 0; i < kSpxForsTrees; i++) {
    indices[i] = 0;
    for (size_t j = 0; j < kSpxForsHeight; j++) {
      indices[i] ^= ((m[offset >> 3] >> (offset & 0x7u)) & 0x1u) << j;
      offset++;
    }
  }
}

rom_error_t fors_pk_from_sig(const uint32_t *sig, const uint8_t *m,
                             const spx_ctx_t *ctx, const spx_addr_t *fors_addr,
                             uint32_t *pk) {
  // Initialize the FORS tree address.
  spx_addr_t fors_tree_addr = {.addr = {0}};
  spx_addr_keypair_copy(&fors_tree_addr, fors_addr);
  spx_addr_type_set(&fors_tree_addr, kSpxAddrTypeForsTree);

  // Initialize the FORS public key address.
  spx_addr_t fors_pk_addr = {.addr = {0}};
  spx_addr_keypair_copy(&fors_pk_addr, fors_addr);
  spx_addr_type_set(&fors_pk_addr, kSpxAddrTypeForsPk);

  uint32_t indices[kSpxForsTrees];
  message_to_indices(m, indices);

  uint32_t roots[kSpxForsTrees * kSpxNWords];
  for (size_t i = 0; i < kSpxForsTrees; i++) {
    uint32_t idx_offset = i * (1 << kSpxForsHeight);

    spx_addr_tree_height_set(&fors_tree_addr, 0);
    spx_addr_tree_index_set(&fors_tree_addr, indices[i] + idx_offset);

    // Derive the leaf from the included secret key part.
    uint32_t leaf[kSpxNWords];
    HARDENED_RETURN_IF_ERROR(fors_sk_to_leaf(sig, ctx, &fors_tree_addr, leaf));
    sig += kSpxNWords;

    // Derive the corresponding root node of this tree.
    uint32_t *root = &roots[i * kSpxNWords];
    HARDENED_RETURN_IF_ERROR(
        spx_utils_compute_root(leaf, indices[i], idx_offset, sig,
                               kSpxForsHeight, ctx, &fors_tree_addr, root));
    sig += kSpxNWords * kSpxForsHeight;
  }

  // Hash horizontally across all tree roots to derive the public key.
  return thash(roots, kSpxForsTrees, ctx, &fors_pk_addr, pk);
}
