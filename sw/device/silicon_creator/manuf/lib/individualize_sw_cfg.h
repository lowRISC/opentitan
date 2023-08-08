// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img.h"

/**
 * OTP Creator Software Configuration Partition.
 */
extern const size_t kOtpKvCreatorSwCfgSize;
extern const otp_kv_t kOtpKvCreatorSwCfg[];

/**
 * OTP Owner Software Configuration Partition.
 */
extern const size_t kOtpKvOwnerSwCfgSize;
extern const otp_kv_t kOtpKvOwnerSwCfg[];

/**
 * Configures the CREATOR_SW_CFG and OWNER_SW_CFG OTP partitions.
 *
 * The CREATOR_SW_CFG and OWNER_SW_CFG partitions contain various settings for
 * the ROM, for example:
 * - ROM key enable/disable flags
 * - Alert handler configuration
 * - AST and entropy complex configuration
 * - Various ROM feature knobs
 *
 * Note: The operation will fail if there are any pre-programmed words not equal
 * to the expected test values.
 *
 * The caller should reset the device after calling this function to verify that
 * the ROM is able to boot with the new configuration.
 *
 * @param otp_ctrl OTP controller instance.
 * @return OK_STATUS if the HW_CFG partition is locked.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_individualize_device_sw_cfg(const dif_otp_ctrl_t *otp_ctrl);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_
