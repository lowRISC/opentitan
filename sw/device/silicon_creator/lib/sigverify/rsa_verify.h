// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_VERIFY_H_

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Verifies an RSASSA-PKCS1-v1_5 signature.
 *
 * The actual implementation that is used (software or OTBN) is determined by
 * the life cycle state of the device and the OTP value.
 *
 * @param signature Signature to be verified.
 * @param key Signer's RSA public key.
 * @param act_digest Actual digest of the message being verified.
 * @param lc_state Life cycle state of the device.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
rom_error_t sigverify_rsa_verify(const sigverify_rsa_buffer_t *signature,
                                 const sigverify_rsa_key_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state,
                                 uint32_t *flash_exec);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_RSA_VERIFY_H_
