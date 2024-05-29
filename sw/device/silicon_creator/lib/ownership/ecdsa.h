// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ECDSA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ECDSA_H_

#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes ECDSA crypto.
 */
rom_error_t ecdsa_init(void);

/**
 * Verifies an ECDSA P-256 signature.
 *
 * @param pubkey The public key needed to verify the signature
 * expressed as 32-bit little endian words: (le(X) || le(Y)).
 * @param signature The signature expressed as 32-bit little
 * endian words: (le(R) || le(S))
 * @param digest The digest of the message to verify.
 * @return hardened_bool_t
 */

hardened_bool_t ecdsa_verify_digest(const owner_key_t *pubkey,
                                    const owner_signature_t *signature,
                                    const hmac_digest_t *digest);

/**
 * Verifies an ECDSA P-256 signature.
 *
 * @param pubkey The public key needed to verify the signature
 * expressed as 32-bit little endian words: (le(X) || le(Y)).
 * @param signature The signature expressed as 32-bit little
 * endian words: (le(R) || le(S))
 * @param message The message to verify.
 * @param message_len The length of the message to verify.
 * @return hardened_bool_t
 */
hardened_bool_t ecdsa_verify_message(const owner_key_t *pubkey,
                                     const owner_signature_t *signature,
                                     const void *message, size_t message_len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ECDSA_H_
