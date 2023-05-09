// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/fors.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_FORS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_FORS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Derives the FORS public key from a signature.
 *
 * This can be used for verification by comparing to a known public key, or to
 * subsequently verify a signature on the derived public key. The latter is the
 * typical use-case when used as an FTS below an OTS in a hypertree. Assumes m
 * contains at least kSpxForsHeight * kSpxForsTrees bits.
 *
 * @param sig FORS signature.
 * @param m Message corresponding to the signature.
 * @param ctx Context object.
 * @param fors_addr A FORS tree address.
 * @param[out] pk Resulting public key.
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t fors_pk_from_sig(const uint32_t *sig, const uint8_t *m,
                             const spx_ctx_t *ctx, const spx_addr_t *fors_addr,
                             uint32_t *pk);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_FORS_H_
