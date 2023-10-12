// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/json/provisioning_command.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_lc_ctrl_t lc_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

status_t command_processor(ujson_t *uj) {
  LOG_INFO("FT SRAM provisioning start. Waiting for command ...");
  while (true) {
    ft_sram_provisioning_command_t command;
    TRY(ujson_deserialize_ft_sram_provisioning_command_t(uj, &command));
    switch (command) {
      case kFtSramProvisioningCommandWriteAll:
        LOG_INFO("Writing both *_SW_CFG OTP partitions ...");
        CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg(&otp_ctrl));
        CHECK_STATUS_OK(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
        break;
      case kFtSramProvisioningCommandOtpCreatorSwCfgWrite:
        LOG_INFO("Writing the CREATOR_SW_CFG OTP partition ...");
        CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg(&otp_ctrl));
        break;
      case kFtSramProvisioningCommandOtpOwnerSwCfgWrite:
        LOG_INFO("Writing the OWNER_SW_CFG OTP partition ...");
        CHECK_STATUS_OK(manuf_individualize_device_owner_sw_cfg(&otp_ctrl));
        break;
      case kFtSramProvisioningCommandDone:
        LOG_INFO("FT SRAM provisioning done.");
        return RESP_OK_STATUS(uj);
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
    RESP_OK_STATUS(uj);
  }
  // We should never reach here.
  return INTERNAL();
}

bool sram_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
  ujson_t uj = ujson_ottf_console();

  // Check we are in in TEST_UNLOCKED1.
  CHECK_STATUS_OK(
      lc_ctrl_testutils_check_lc_state(&lc_ctrl, kDifLcCtrlStateTestUnlocked1));

  // Process provisioning commands.
  CHECK_STATUS_OK(command_processor(&uj));

  return true;
}
