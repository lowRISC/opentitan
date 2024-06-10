// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/context.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Context object for the SPHINCS+ operation.
 *
 * The reference implementation stores `sk_seed` here as well, but we only
 * performing verification so we don't need it.
 */
typedef struct spx_ctx {
  /**
   * Public key seed.
   */
  uint32_t pub_seed[kSpxNWords];
  /**
   * SHA256 state that absorbed pub_seed and padding.
   */
  hmac_context_t state_seeded;
} spx_ctx_t;

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_CONTEXT_H_
