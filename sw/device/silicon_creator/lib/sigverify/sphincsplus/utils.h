// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/utils.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_UTILS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_UTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Convert from big-endian bytes to a 64-bit integer.
 *
 * It is the caller's responsibility to ensure the number of bytes is small
 * enough to fit a 64-bit integer (i.e. `inlen` <= 8).
 *
 * Appears in the reference code as `bytes_to_ull`.
 *
 * @param in Input buffer
 * @param inlen Size of input buffer (in bytes).
 */
uint64_t spx_utils_bytes_to_u64(const uint8_t *in, size_t inlen);

/**
 * Computes a root node of a subtree.
 *
 * Computes the root node based on the provided leaf and authentication path.
 * Expects address to be complete other than the tree_height and tree_index.
 *
 * @param leaf Input leaf.
 * @param leaf_idx Index of input leaf.
 * @param idx_offset Leaf index offset.
 * @param auth_path Input authentication path.
 * @param tree_height Tree height.
 * @param ctx Context object.
 * @param addr Hypertree address.
 * @param[out] root Resulting root node.
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spx_utils_compute_root(const uint32_t *leaf, uint32_t leaf_idx,
                                   uint32_t idx_offset,
                                   const uint32_t *auth_path,
                                   uint8_t tree_height, const spx_ctx_t *ctx,
                                   spx_addr_t *addr, uint32_t *root);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_UTILS_H_
