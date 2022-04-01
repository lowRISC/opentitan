// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Correct `flash_exec` value.
   *
   * This value must be equal to `FLASH_CTRL_PARAM_EXEC_EN`. Defined here to be
   * able to use in tests.
   */
  kSigverifyFlashExec = 0xa26a38f7,
};

/**
 * Gets the ID of an RSA public key from its modulus.
 *
 * ID of a key is the least significant word of its modulus.
 * Callers must make sure that `modulus` is valid before calling this function.
 *
 * @param key An RSA public key.
 * @return ID of the key.
 */
inline uint32_t sigverify_rsa_key_id_get(
    const sigverify_rsa_buffer_t *modulus) {
  return modulus->data[0];
}

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

/**
 * Gets the usage constraints struct that is used for verifying a ROM_EXT.
 *
 * This function reads
 * - The device identifier from the life cycle controller,
 * - Creator and owner manufacturing states from the OTP,
 * - The life cycle state from life cycle controller, and
 * masks the fields of `usage_constraints` according to the given
 * `selector_bits`.
 *
 * See also: `manifest_usage_constraints_t`.
 *
 * @param selector_bits Selector bits of the manifest of the ROM_EXT to be
 * verified.
 * @param[out] usage_constraints Usage constraints.
 */
void sigverify_usage_constraints_get(
    uint32_t selector_bits, manifest_usage_constraints_t *usage_constraints);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SIGVERIFY_H_
