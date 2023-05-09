// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/sign.c

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/fors.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/utils.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/wots.h"

static_assert(kSpxVerifySigWords * sizeof(uint32_t) == kSpxVerifySigBytes,
              "kSpxVerifySigWords and kSpxVerifySigBytes do not match.");
static_assert(kSpxVerifyPkWords * sizeof(uint32_t) == kSpxVerifyPkBytes,
              "kSpxVerifyPkWords and kSpxVerifyPkBytes do not match.");
static_assert(kSpxD <= UINT8_MAX, "kSpxD must fit into a uint8_t.");
rom_error_t spx_verify(const uint32_t *sig, const uint8_t *msg_prefix_1,
                       size_t msg_prefix_1_len, const uint8_t *msg_prefix_2,
                       size_t msg_prefix_2_len, const uint8_t *msg,
                       size_t msg_len, const uint32_t *pk, uint32_t *root) {
  spx_ctx_t ctx;
  memcpy(ctx.pub_seed, pk, kSpxN);

  // This hook allows the hash function instantiation to do whatever
  // preparation or computation it needs, based on the public seed.
  HARDENED_RETURN_IF_ERROR(spx_hash_initialize(&ctx));

  spx_addr_t wots_addr = {.addr = {0}};
  spx_addr_t tree_addr = {.addr = {0}};
  spx_addr_t wots_pk_addr = {.addr = {0}};
  spx_addr_type_set(&wots_addr, kSpxAddrTypeWots);
  spx_addr_type_set(&tree_addr, kSpxAddrTypeHashTree);
  spx_addr_type_set(&wots_pk_addr, kSpxAddrTypeWotsPk);

  // Derive the message digest and leaf index from R || PK || M.
  // The additional kSpxN is a result of the hash domain separator.
  uint8_t mhash[kSpxForsMsgBytes];
  uint64_t tree;
  uint32_t idx_leaf;
  HARDENED_RETURN_IF_ERROR(spx_hash_message(
      sig, pk, msg_prefix_1, msg_prefix_1_len, msg_prefix_2, msg_prefix_2_len,
      msg, msg_len, mhash, &tree, &idx_leaf));
  sig += kSpxNWords;

  // Layer correctly defaults to 0, so no need to set_layer_addr.
  spx_addr_tree_set(&wots_addr, tree);
  spx_addr_keypair_set(&wots_addr, idx_leaf);

  HARDENED_RETURN_IF_ERROR(
      fors_pk_from_sig(sig, mhash, &ctx, &wots_addr, root));
  sig += kSpxForsWords;

  // For each subtree..
  for (uint8_t i = 0; i < kSpxD; i++) {
    spx_addr_layer_set(&tree_addr, i);
    spx_addr_tree_set(&tree_addr, tree);

    spx_addr_subtree_copy(&wots_addr, &tree_addr);
    spx_addr_keypair_set(&wots_addr, idx_leaf);

    spx_addr_keypair_copy(&wots_pk_addr, &wots_addr);

    // The WOTS public key is only correct if the signature was correct.
    // Initially, root is the FORS pk, but on subsequent iterations it is
    // the root of the subtree below the currently processed subtree.
    uint32_t wots_pk[kSpxWotsWords];
    HARDENED_RETURN_IF_ERROR(
        wots_pk_from_sig(sig, root, &ctx, &wots_addr, wots_pk));
    sig += kSpxWotsWords;

    // Compute the leaf node using the WOTS public key.
    uint32_t leaf[kSpxNWords];
    HARDENED_RETURN_IF_ERROR(
        thash(wots_pk, kSpxWotsLen, &ctx, &wots_pk_addr, leaf));

    // Compute the root node of this subtree.
    HARDENED_RETURN_IF_ERROR(spx_utils_compute_root(
        leaf, idx_leaf, 0, sig, kSpxTreeHeight, &ctx, &tree_addr, root));
    sig += kSpxTreeHeight * kSpxNWords;

    // Update the indices for the next layer.
    idx_leaf = (tree & ((1 << kSpxTreeHeight) - 1));
    tree = tree >> kSpxTreeHeight;
  }

  return kErrorOk;
}

inline void spx_public_key_root(const uint32_t *pk, uint32_t *root) {
  memcpy(root, pk + kSpxNWords, kSpxN);
}
