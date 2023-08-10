// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_PREOP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_PREOP_H_

#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Configures the CREATOR_SW an OWNER_SW OTP partitions.
 *
 * The CREATOR_SW and OWNER_SW partitions contain various settings for the ROM,
 * for example:
 * - ROM key enable/disable flags
 * - Alert handler configuration
 * - AST and entropy complex configuration
 * - Various ROM feature knobs
 *
 * Note: The test will fail if there are any pre-programmed words not equal to
 * the expected test values.
 *
 * The caller should reset the device after calling this function to verify that
 * the ROM is able to boot with the new configuration.
 *
 * @param otp OTP controller instance.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t individualize_preop_otp_write(const dif_otp_ctrl_t *otp);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_INDIVIDUALIZE_PREOP_H_
