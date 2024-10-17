// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "otp_ctrl_regs.h"  // Generated.

/**
 * Configures the SECRET1 OTP partition.
 *
 * The SECRET1 partition contains the Flash and SRAM scrambling seeds for the
 * device.
 *
 * Preconditions:
 * - Device has SW CSRNG data access (configured in HW_CFG0 parition).
 *
 * Note: The test will skip all programming steps and succeed if the SECRET1
 * parition is already locked. This is to facilitate test re-runs.
 *
 * The caller should reset the device after calling this function and call
 * `manuf_personalize_device_secret1_check()` afterwards to confirm that the
 * OTP partition was successfully locked.
 *
 * @param lc_ctrl Lifecycle controller instance.
 * @param otp_ctrl OTP controller instance.
 * @return OK_STATUS on success.
 */
status_t manuf_personalize_device_secret1(const dif_lc_ctrl_t *lc_ctrl,
                                          const dif_otp_ctrl_t *otp_ctrl);

/**
 * Checks the SECRET1 OTP partition end state.
 *
 * @param otp_ctrl OTP controller interface.
 * @return OK_STATUS if the SECRET1 partition is locked.
 */
status_t manuf_personalize_device_secret1_check(const dif_otp_ctrl_t *otp_ctrl);

/**
 * Personalize device with unique secrets.
 *
 * The device is provisioned with a unique set of secrets, which are hidden from
 * software. These secrets include both:
 *
 * 1. roots of the key derivation function in the key manager,
 *   a. CreatorSeed (Flash - Info Page)
 *   b. OwnerSeed (Flash - Info Page)
 *   c. RootKey (OTP - SECRET2 Partition)
 * 2. the RMA unlock token (OTP - SECRET2 Partition)
 *
 * Preconditions:
 * - Device has SW CSRNG data access (configured in HW_CFG0 parition).
 *
 * Note: The test will skip all programming steps and succeed if the SECRET2
 * partition is already locked. This is to facilitate test re-runs.
 *
 * The caller should reset the device after calling this function.
 *
 * @param flash_state Flash controller instance.
 * @param lc_ctrl Lifecycle controller instance.
 * @param otp_ctrl OTP controller instance.
 * @param rma_unlock_token_hash Pointer to the hashed RMA unlock token.
 * @return OK_STATUS on success.
 */
status_t manuf_personalize_device_secrets(
    dif_flash_ctrl_state_t *flash_state, const dif_lc_ctrl_t *lc_ctrl,
    const dif_otp_ctrl_t *otp_ctrl,
    const lc_token_hash_t *rma_unlock_token_hash);

/**
 * Personalize device with an asymmetric keygen seed.
 *
 * The device is provisioned with a unique seed (extracted from a CSRNG
 * instance) in the provided flash info page field that can be used at runtime
 * to generate an asymmetric (e.g., ECDSA) key pair.
 *
 * Preconditions:
 * - Device has SW CSRNG data access (configured in HW_CFG0 parition).
 * - Device has initialized the entropy complex.
 *
 * @param flash_state Flash controller instance.
 * @param field Info flash field location information.
 * @param len The number of uint32_t words to program starting at the beginning
 *            of the target flash info field.
 * @return OK_STATUS on success.
 */
status_t manuf_personalize_flash_asymm_key_seed(
    dif_flash_ctrl_state_t *flash_state, flash_info_field_t field, size_t len);

/**
 * Checks the device personalization end state.
 *
 * When personalization is complete, OTP SECRET2 partition should be locked.
 *
 * @param otp_ctrl OTP controller instance.
 * @return OK_STATUS if the SECRET2 OTP partition is locked.
 */
status_t manuf_personalize_device_secrets_check(const dif_otp_ctrl_t *otp_ctrl);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_PERSONALIZE_H_
