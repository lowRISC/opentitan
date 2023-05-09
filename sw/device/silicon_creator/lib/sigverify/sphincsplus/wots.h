// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/wots.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_WOTS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_WOTS_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Compute a WOTS public key from a signature and message.
 *
 * The caller is responsible for ensuring `kSpxWotsPkWords` of space are
 * available at `pk`.
 *
 * @param sig Input signature (`kSpxWotsBytes` bytes).
 * @param msg Input message (`kSpxWotsLen1 * kSpxWotsLogW` bytes).
 * @param ctx Context object.
 * @param addr Hypertree address.
 * @param[out] pk Resulting WOTS public key.
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t wots_pk_from_sig(const uint32_t *sig, const uint32_t *msg,
                             const spx_ctx_t *ctx, spx_addr_t *addr,
                             uint32_t *pk);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_WOTS_H_
