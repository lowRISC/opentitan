// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_command.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;

/**
 * Initializes all DIF handles used in this SRAM program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  return OK_STATUS();
}

status_t command_processor(ujson_t *uj) {
  LOG_INFO("FT personalization start. Waiting for command ...");
  while (true) {
    ft_personalize_command_t command;
    TRY(ujson_deserialize_ft_personalize_command_t(uj, &command));
    switch (command) {
      case kFtPersonalizeCommandDone:
        LOG_INFO("FT personalization done.");
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

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();

  // Check we are in a mission mode LC state (i.e., DEV, PROD, or PROD_END).
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));

  // Check {CREATOR,OWNER}_SW_CFG and HW_CFG OTP partitions have been locked.
  CHECK_STATUS_OK(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl));
  CHECK_STATUS_OK(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl));
  CHECK_STATUS_OK(manuf_individualize_device_hw_cfg_check(&otp_ctrl));

  // Process provisioning commands.
  CHECK_STATUS_OK(command_processor(&uj));

  return true;
}
