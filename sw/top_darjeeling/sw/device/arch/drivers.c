// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/csrng/driver/csrng.h"
#include "sw/ip/edn/driver/edn.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/keymgr/driver/keymgr.h"
#include "sw/ip/kmac/driver/kmac.h"
#include "sw/ip/lc_ctrl/driver/lc_ctrl.h"
#include "sw/ip/otp_ctrl/driver/otp_ctrl.h"
#include "sw/ip/pinmux/driver/pinmux.h"
#include "sw/ip/rstmgr/driver/rstmgr.h"
#include "sw/ip/rv_core_ibex/driver/rv_core_ibex.h"
#include "sw/ip/sram_ctrl/driver/sram_ctrl.h"
#include "sw/ip/uart/driver/uart.h"

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

const uint32_t kLcCtrlRegsBaseAddr[] = {TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR};

const uint32_t kOtpCtrlCoreBaseAddr[] = {
    TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR};

const uint32_t kPinmuxAonBaseAddr[] = {TOP_DARJEELING_PINMUX_AON_BASE_ADDR};

const uint32_t kRstmgrAonBaseAddr[] = {TOP_DARJEELING_RSTMGR_AON_BASE_ADDR};

const uint32_t kRvCoreIbexCfgBaseAddr[] = {
    TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR};

const uint32_t kSramCtrlMainRegsBaseAddr[] = {
    TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR};

const uint32_t kUartBaseAddr[] = {TOP_DARJEELING_UART0_BASE_ADDR};
