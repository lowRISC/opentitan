// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rv_dm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kRvDmEnableVal = kMultiBitBool32True,

  kDebugEnableDelayMicrosDvSim = 1000,  // 1ms

  // For FPGA and silicon, we need to wait long enough for opentitantoolib to
  // return an error when trying to perform an operation on the device when
  // debug mode is not enabled.
  kDebugEnableDelayMicrosDefault = 1000000,  // 1s
};

static dif_lc_ctrl_t lc_ctrl;
static dif_rv_dm_t rv_dm;

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));

  CHECK_DIF_OK(dif_rv_dm_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_DM_REGS_BASE_ADDR), &rv_dm));

  dif_lc_ctrl_state_t state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &state));
  CHECK_STATUS_OK(lc_ctrl_testutils_lc_state_log(&state));

  if (state == kDifLcCtrlStateDev) {
    bool is_locked;
    CHECK_DIF_OK(dif_rv_dm_late_debug_is_locked(&rv_dm, &is_locked));

    // Until we add support for delayed enable to the ROM_EXT, we expect this
    // feature to be unlocked.
    CHECK(!is_locked);

    uint32_t delay_micros = kDebugEnableDelayMicrosDefault;
    if (kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSimVerilator) {
      delay_micros = kDebugEnableDelayMicrosDvSim;
    }

    CHECK_DIF_OK(dif_rv_dm_late_debug_configure(&rv_dm, kDifToggleDisabled));
    LOG_INFO("DEBUG_MODE_DISABLED");
    busy_spin_micros(delay_micros);

    // Enable debug mode. Report enablement via UART and busy spin again to
    // allow the debugger to attach.
    CHECK_DIF_OK(dif_rv_dm_late_debug_configure(&rv_dm, kDifToggleEnabled));

    // The following string is expected in host side of the test.
    LOG_INFO("DEBUG_MODE_ENABLED");
    busy_spin_micros(delay_micros);
  }

  return true;
}
