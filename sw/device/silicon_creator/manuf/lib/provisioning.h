// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"

#include "otp_ctrl_regs.h"  // Generated.

enum {
  /**
   * RMA unlock token sizes and offsets.
   */
  kRmaUnlockTokenSizeInBytes = OTP_CTRL_PARAM_RMA_TOKEN_SIZE,
  kRmaUnlockTokenSizeIn32BitWords =
      kRmaUnlockTokenSizeInBytes / sizeof(uint32_t),
  kRmaUnlockTokenSizeIn64BitWords =
      kRmaUnlockTokenSizeInBytes / sizeof(uint64_t),
};

/**
 * Wrapped (encrypted) RMA unlock token.
 *
 * The RMA unlock token is encrypted with AES using an ECDH emphemeral key. The
 * key wrapping process works as follows:
 *
 * - An HSM generates an ECDH-P256 keypair (`sk_hsm`, `pk_hsm`), where the
 *   public component, `pk_hsm`, is baked into the provisioning test program.
 * - During provisioning, the device generates an additional ECDH-P256 keypair
 *   (`sk_device`, `pk_device`).
 * - The device then generates an emphemeral shared AES key (`k_shared`) using
 *   `sk_device` and `pk_hsm`.
 * - The device encrypts the raw RMA unlock token using AES and the shared
 *   secret key, `k_shared`.
 * - The device transmits the encrypted RMA unlock token, along with the
 *   device-generated `pk_device`, to the host (e.g. ATE), allowing the RMA
 *   unlock token to be decrypted using the shared secret (`k_shared`) derived
 *   by the HSM.
 */
typedef struct wrapped_rma_unlock_token {
  /**
   * Encrypted RMA unlock token to export from the device.
   */
  uint32_t data[kRmaUnlockTokenSizeIn32BitWords];
  /**
   * Device generated ECDH public key matching the private key used to generate
   * an emphemeral AES ECB key.
   */
  uint32_t ecc_pk_device_x[kP256CoordWords];
  uint32_t ecc_pk_device_y[kP256CoordWords];
} wrapped_rma_unlock_token_t;

/**
 * Run device personalization.
 *
 * The device is configured with a unique set of secrets, which once
 * provisioned, are hidden from software. These secrets are used as the root
 * of the key derivation function in the key manager.
 *
 * This function implements part of the
 * `manuf_ft_provision_rma_token_and_personalization` testpoint documented in
 * the sw/device/silicon_creator/manuf/data/manuf_testplan.hjson testplan.
 *
 * Preconditions:
 * - Device is in DEV, PROD, or PROD_END lifecycle stage.
 * - Device has SW CSRNG data access.
 *
 * Note: The test will skip all programming steps and succeed if the SECRET2
 * partition is already locked. This is to facilitate test re-runs.
 *
 * The caller should reset the device after calling this function.
 *
 * @param flash_state Flash controller instance.
 * @param lc_ctrl Lifecycle controller instance.
 * @param otp OTP controller instance.
 * @param[out] wrapped_token Wrapped RMA unlock token.
 * @return OK_STATUS on success.
 */
status_t provisioning_device_secrets_start(
    dif_flash_ctrl_state_t *flash_state, const dif_lc_ctrl_t *lc_ctrl,
    const dif_otp_ctrl_t *otp, wrapped_rma_unlock_token_t *wrapped_token);
/**
 * Checks device personalization end state.
 *
 * @param otp OTP controller instance.
 * @return OK_STATUS if the SECRET2 OTP partition is locked.
 */
status_t provisioning_device_secrets_end(const dif_otp_ctrl_t *otp);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_
