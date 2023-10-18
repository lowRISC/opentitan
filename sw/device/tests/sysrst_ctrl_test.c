// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/sysrst_ctrl.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/pinmux_config.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_pinmux_t pinmux;

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandPinmuxConfig:
        RESP_ERR(uj, pinmux_config(uj, &pinmux));
        break;
      case kTestCommandSysrstCtrlCommand:
        RESP_ERR(uj, sysrst_ctrl_command(uj, &sysrst_ctrl));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  // We should never reach here.
  return INTERNAL();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));

  mmio_region_write32(sysrst_ctrl.base_addr,
                        SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
                        0);
  // Make sure the the DIO pins EC reset and flash WP are configured correctly.
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      // FIXME OpenDrain does not work (rejected by hardware)
      .flags = kDifPinmuxPadAttrVirtualOpenDrain,
  };
  LOG_INFO("Configure pin");
  dif_result_t res = dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSysrstCtrlAonEcRstL,
                                          kDifPinmuxPadKindDio, in_attr, &out_attr);
  LOG_INFO("res=%d, attrs: in={%d,%d,%x}, out={%d,%d,%x}", res,
           in_attr.slew_rate, in_attr.drive_strength, in_attr.flags,
           out_attr.slew_rate, out_attr.drive_strength, out_attr.flags);
  CHECK_DIF_OK(res);
  res = dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSysrstCtrlAonFlashWpL,
                                          kDifPinmuxPadKindDio, in_attr, &out_attr);
  LOG_INFO("res=%d, attrs: in={%d,%d,%x}, out={%d,%d,%x}", res,
           in_attr.slew_rate, in_attr.drive_strength, in_attr.flags,
           out_attr.slew_rate, out_attr.drive_strength, out_attr.flags);
  CHECK_DIF_OK(res);

  ujson_t uj = ujson_ottf_console();

  status_t s = command_processor(&uj);
  LOG_INFO("status = %r", s);
  return status_ok(s);
}
