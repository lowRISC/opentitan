// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/context.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Context object for the SPHINCS+ operation.
 *
 * The reference implementation has more fields here: `sk_seed` and
 * hash-specific precomputed values for Haraka and SHA2 hash functions. Since
 * we are only using SHAKE-based SPHINCS+ in this context, and only performing
 * verification, all we need is the public key seed.
 */
typedef struct spx_ctx {
  uint32_t pub_seed[kSpxNWords];
} spx_ctx_t;

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_
