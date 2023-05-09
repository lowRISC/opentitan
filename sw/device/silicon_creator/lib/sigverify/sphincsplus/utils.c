// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/utils.c

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/utils.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"

uint64_t spx_utils_bytes_to_u64(const uint8_t *in, size_t inlen) {
  uint64_t retval = 0;
  for (size_t i = 0; i < inlen; i++) {
    retval |= ((uint64_t)in[i]) << (8 * (inlen - 1 - i));
  }
  return retval;
}

rom_error_t spx_utils_compute_root(const uint32_t *leaf, uint32_t leaf_idx,
                                   uint32_t idx_offset,
                                   const uint32_t *auth_path,
                                   uint8_t tree_height, const spx_ctx_t *ctx,
                                   spx_addr_t *addr, uint32_t *root) {
  // Initialize working buffer.
  uint32_t buffer[2 * kSpxNWords];
  // Pointer to second half of buffer for convenience.
  uint32_t *buffer_second = &buffer[kSpxNWords];

  // If leaf_idx is odd (last bit = 1), current path element is a right child
  // and auth_path has to go left. Otherwise it is the other way around.
  if (leaf_idx & 1) {
    memcpy(buffer_second, leaf, kSpxN);
    memcpy(buffer, auth_path, kSpxN);
  } else {
    memcpy(buffer, leaf, kSpxN);
    memcpy(buffer_second, auth_path, kSpxN);
  }
  auth_path += kSpxNWords;

  for (uint8_t i = 0; i < tree_height - 1; i++) {
    leaf_idx >>= 1;
    idx_offset >>= 1;
    // Set the address of the node we're creating.
    spx_addr_tree_height_set(addr, i + 1);
    spx_addr_tree_index_set(addr, leaf_idx + idx_offset);

    // Pick the right or left neighbor, depending on parity of the node.
    uint32_t *hash_dst = (leaf_idx & 1) ? buffer_second : buffer;
    uint32_t *auth_dst = (leaf_idx & 1) ? buffer : buffer_second;

    // This is an inlined `thash` operation.
    HARDENED_RETURN_IF_ERROR(kmac_shake256_start());
    kmac_shake256_absorb_words(ctx->pub_seed, kSpxNWords);
    kmac_shake256_absorb_words(addr->addr, ARRAYSIZE(addr->addr));
    kmac_shake256_absorb_words(buffer, 2 * kSpxNWords);
    kmac_shake256_squeeze_start();

    // Copy the auth path while KMAC is processing for performance reasons.
    memcpy(auth_dst, auth_path, kSpxN);
    auth_path += kSpxNWords;

    // Get the `thash` output.
    HARDENED_RETURN_IF_ERROR(kmac_shake256_squeeze_end(hash_dst, kSpxNWords));
  }

  // The last iteration is exceptional; we do not copy an auth_path node.
  leaf_idx >>= 1;
  idx_offset >>= 1;
  spx_addr_tree_height_set(addr, tree_height);
  spx_addr_tree_index_set(addr, leaf_idx + idx_offset);
  return thash(buffer, 2, ctx, addr, root);
}
