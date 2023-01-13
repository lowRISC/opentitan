// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/api.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_VERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Size of SPHINCS+ root node.
   */
  kSpxVerifyRootNumWords = kSpxNWords,
  /**
   * Size of SPHINCS+ signature.
   */
  kSpxVerifySigBytes = kSpxBytes,
  /**
   * Size of SPHINCS+ public key.
   */
  kSpxVerifyPkBytes = kSpxPkBytes,
};

/**
 * Computes the root for a signature and message under a given public key.
 *
 * The signature is valid if the computed root matches the root from the public
 * key; the final comparison is left to the caller.
 *
 * @param sig Input signature (`kSpxVerifySigBytes` bytes long).
 * @param m Input message.
 * @param mlen Length of message (bytes).
 * @param pk Public key (`kSpxVerifyPkBytes` bytes long).
 * @param[out] root Buffer for computed tree root (`kSpxVerifyRootNumWords`
 *                  words long).
 * @return Error code indicating if the operation succeeded.
 */
OT_WARN_UNUSED_RESULT
rom_error_t spx_verify(const uint8_t *sig, const uint8_t *m, size_t mlen,
                       const uint8_t *pk, uint32_t *root);

/**
 * Extract the public key root.
 *
 * @param pk Public key (`kSpxVerifyPkBytes` bytes long).
 * @param[out] root Buffer for the public key root (`kSpxVerifyRootNumWords`
 *                  words long).
 */
void spx_public_key_root(const uint8_t *pk, uint32_t *root);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_VERIFY_H_
