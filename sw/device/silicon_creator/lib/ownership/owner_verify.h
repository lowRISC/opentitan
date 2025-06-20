// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_VERIFY_H_

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/spx_key.h"

/**
 * Verify data using an owner key or owner application key.
 *
 * @param key_alg The key algorithm (i.e.: ownership_key_alg_t).
 * @param key The public key material.
 * @param ecdsa_sig The ECDSA signature to verify (if relevant to key_alg).
 * @param spx_sig The SPX signature to verify (if relevant to key_alg).
 * @param msg_prefix_1 A portion of the SPX+ message to verify (if relevant).
 * @param msg_prefix_1_len The length of msg_prefix_1.
 * @param msg_prefix_2 A portion of the SPX+ message to verify (if relevant).
 * @param msg_prefix_2_len The length of msg_prefix_2.
 * @param msg The SPX+ message to verify (if relevant).
 * @param msg_len The length of the msg.
 * @param digest The SHA256 digest over the data to verify.
 * @param flash_exec[out] The flash_exec password, if the verify succeeds.
 * @return kErrorOk if the verify succeeds, else an error code.
 */
rom_error_t owner_verify(uint32_t key_alg, const owner_keydata_t *key,
                         const ecdsa_p256_signature_t *ecdsa_sig,
                         const sigverify_spx_signature_t *spx_sig,
                         const void *msg_prefix_1, size_t msg_prefix_1_len,
                         const void *msg_prefix_2, size_t msg_prefix_2_len,
                         const void *msg, size_t msg_len,
                         const hmac_digest_t *digest, uint32_t *flash_exec);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_VERIFY_H_
