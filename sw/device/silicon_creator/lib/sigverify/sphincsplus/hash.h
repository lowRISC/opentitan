// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/hash.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_HASH_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_HASH_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize the SPHINCS+ hash function.
 *
 * Hook for any precomputation or setup tasks the hash function needs to do
 * before a SPHINCS+ operation takes place.
 *
 * Appears in reference code as `initialize_hash_function`.
 *
 * @param ctx Context object.
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spx_hash_initialize(spx_ctx_t *ctx);

/**
 * Hash the input message and derive the leaf index.
 *
 * Computes H(R, pk, msg), where R is the random number included in the SPHINCS+
 * signature and H is the underlying hash function (Hmsg in the SPHINCS+
 * paper). Outputs the message digest and the index of the leaf. The index is
 * split in the tree index and the leaf index, for convenient copying to an
 * address.
 *
 * @param R Per-signature random number.
 * @param pk Public key.
 * @param msg_prefix_1 Optional message prefix.
 * @param msg_prefix_1_len Length of the first prefix.
 * @param msg_prefix_2 Optional message prefix.
 * @param msg_prefix_2_len Length of the second prefix.
 * @param msg Input message.
 * @param msg_len Input message length.
 * @param[out] digest Output buffer for message digest.
 * @param[out] tree Tree index.
 * @param[out] leaf_idx Leaf index.
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spx_hash_message(const uint32_t *R, const uint32_t *pk,
                             const uint8_t *msg_prefix_1,
                             size_t msg_prefix_1_len,
                             const uint8_t *msg_prefix_2,
                             size_t msg_prefix_2_len, const uint8_t *msg,
                             size_t msg_len, uint8_t *digest, uint64_t *tree,
                             uint32_t *leaf_idx);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_HASH_H_
