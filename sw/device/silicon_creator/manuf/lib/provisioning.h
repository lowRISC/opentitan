// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_

#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/base/status.h"

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
 * @param[out] export_data UJSON struct of data to export from the device.
 * @return OK_STATUS on success.
 */
status_t provisioning_device_secrets_start(dif_flash_ctrl_state_t *flash_state,
                                           const dif_lc_ctrl_t *lc_ctrl,
                                           const dif_otp_ctrl_t *otp,
                                           manuf_provisioning_t *export_data);

/**
 * Checks device personalization end state.
 *
 * @param otp OTP controller instance.
 * @return OK_STATUS if the SECRET2 OTP partition is locked.
 */
status_t provisioning_device_secrets_end(const dif_otp_ctrl_t *otp);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PROVISIONING_H_
