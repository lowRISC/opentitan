// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/csrng/driver/csrng.h"
#include "sw/ip/edn/driver/edn.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/keymgr/driver/keymgr.h"
#include "sw/ip/kmac/driver/kmac.h"
#include "sw/ip/otp_ctrl/driver/otp_ctrl.h"
#include "sw/ip/rstmgr/driver/rstmgr.h"
#include "sw/ip/usbdev/driver/usbdev.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

/**
 * @file
 * @brief Device-specific driver definitions
 */

const uint32_t kCsrngBaseAddr[] = {TOP_DARJEELING_CSRNG_BASE_ADDR};

const uint32_t kEdnBaseAddr[] = {TOP_DARJEELING_EDN0_BASE_ADDR,
                                 TOP_DARJEELING_EDN1_BASE_ADDR};

const uint32_t kFlashCtrlCoreBaseAddr[] = {
    TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR};

const uint32_t kFlashCtrlMemBaseAddr[] = {
    TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR};

const uint32_t kKeymgrBaseAddr[] = {TOP_DARJEELING_KEYMGR_BASE_ADDR};

const uint32_t kKmacBaseAddr[] = {TOP_DARJEELING_KMAC_BASE_ADDR};

const uint32_t kOtpCtrlCoreBaseAddr[] = {
    TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR};

const uint32_t kRstmgrAonBaseAddr[] = {TOP_DARJEELING_RSTMGR_AON_BASE_ADDR};

const uint32_t kUsbdevBaseAddr[] = {TOP_DARJEELING_USBDEV_BASE_ADDR};
