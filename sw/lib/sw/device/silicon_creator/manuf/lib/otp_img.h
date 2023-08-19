// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_H_

#include "sw/device/silicon_creator/manuf/lib/otp_img_types.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/base/status.h"

/**
 * Writes OTP values to target OTP `partition`.
 *
 * The `kv` array is preferrably generated using the build infrastructure. See
 * individualize_preop.c and its build target for an example.
 *
 * @param otp OTP Controller instance.
 * @param partition Target OTP partition.
 * @param kv OTP Array of OTP key values. See `otp_kv_t` documentation for more
 * details.
 * @param len Length of the `kv` array.
 * @return OT_WARN_UNUSED_RESULT
 */
OT_WARN_UNUSED_RESULT
status_t otp_img_write(const dif_otp_ctrl_t *otp,
                       dif_otp_ctrl_partition_t partition, const otp_kv_t *kv,
                       size_t len);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_OTP_IMG_H_
