// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/thash.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_THASH_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_THASH_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Tweakable hash function.
 *
 * Produces a digest of length `kSpxN` bytes based on the input buffer,
 * address, and public key seed from `ctx`. The exact construction depends on
 * the SPHINCS+ parameters.
 *
 * For details on tweakable hash constructions for SPHINCS+, see the
 * paper: https://sphincs.org/data/sphincs+-paper.pdf
 *
 * @param in Input buffer.
 * @param inblocks Number of `kSpxN`-byte blocks in input buffer.
 * @param ctx Context object.
 * @param addr Hypertree address.
 * @param[out] out Output buffer (at least `kSpxN` bytes).
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t thash(const uint32_t *in, size_t inblocks, const spx_ctx_t *ctx,
                  const spx_addr_t *addr, uint32_t *out);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_THASH_H_
