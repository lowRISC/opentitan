// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img_types.h"

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
 * Configures the CREATOR_SW_CFG OTP partition.
 *
 * The CREATOR_SW_CFG partition contains various settings for the ROM, e.g.,:
 * - ROM execution enablement
 * - ROM key enable/disable flags
 * - AST and entropy complex configuration
 * - Various ROM feature knobs
 *
 * Note: The operation will fail if there are any pre-programmed words not equal
 * to the expected test values.
 *
 * This partition must be configured, and the chip reset, before the ROM can be
 * booted, thus enabling bootstrap.
 *
 * @param otp_ctrl OTP controller instance.
 * @return OK_STATUS if the HW_CFG partition is locked.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_individualize_device_creator_sw_cfg(
    const dif_otp_ctrl_t *otp_ctrl);

/**
 * Configures the OWNER_SW_CFG OTP partition.
 *
 * The OWNER_SW_CFG partition contains additional settings for the ROM and
 * ROM_EXT, for example:
 * - Alert handler configuration
 * - ROM bootstrap disablement
 * - ROM_EXT bootstrap enablement
 *
 * Note: The operation will fail if there are any pre-programmed words not equal
 * to the expected test values.
 *
 * @param otp_ctrl OTP controller instance.
 * @return OK_STATUS if the HW_CFG partition is locked.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_individualize_device_owner_sw_cfg(
    const dif_otp_ctrl_t *otp_ctrl);

/**
 * Checks the CREATOR_SW_CFG OTP partition end state.
 *
 * @param otp_ctrl OTP controller interface.
 * @return OK_STATUS if the CREATOR_SW_CFG partition is locked.
 */
status_t manuf_individualize_device_creator_sw_cfg_check(
    const dif_otp_ctrl_t *otp_ctrl);

/**
 * Checks the OWNER_SW_CFG OTP partition end state.
 *
 * @param otp_ctrl OTP controller interface.
 * @return OK_STATUS if the OWNER_SW_CFG partition is locked.
 */
status_t manuf_individualize_device_owner_sw_cfg_check(
    const dif_otp_ctrl_t *otp_ctrl);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_SW_CFG_H_
