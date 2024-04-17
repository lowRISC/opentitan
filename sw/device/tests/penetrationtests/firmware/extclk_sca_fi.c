// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/extclk_sca_fi.h"

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/json/extclk_sca_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Switching to external clocks causes the clocks to be unstable for some time.
// This is used to delay further action when the switch happens.
static const int kSettleDelayMicros = 200;

static dif_clkmgr_t clkmgr;

// For passing into `IBEX_SPIN_FOR`.
static bool did_extclk_settle(const dif_clkmgr_t *clkmgr) {
  bool status;
  CHECK_DIF_OK(dif_clkmgr_external_clock_is_settled(clkmgr, &status));
  return status;
}

status_t handle_extclk_sca_fi_configure(ujson_t *uj) {
  penetrationtest_extclk_sca_fi_cfg_t uj_data;
  TRY(ujson_deserialize_penetrationtest_extclk_sca_fi_cfg_t(uj, &uj_data));

  TRY(dif_clkmgr_init(mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
                      &clkmgr));
  LOG_INFO("Configuring Extclk...");

  if (uj_data.sel) {
    if (!uj_data.hi_speed_sel) {
      LOG_INFO("Switching to low speed Extclk...");
    } else {
      LOG_INFO("Switching to high speed Extclk...");
    }
    // Enable external clock.
    TRY(dif_clkmgr_external_clock_set_enabled(&clkmgr, !uj_data.hi_speed_sel));
    // Wait for the external clock to become active.
    IBEX_SPIN_FOR(did_extclk_settle(&clkmgr), kSettleDelayMicros);
    LOG_INFO("External clock enabled.");
  } else {
    // Disable external clock.
    LOG_INFO("Manually reset the device to switch back to internal clock.");
  }

  return OK_STATUS();
}

status_t handle_extclk_sca_fi(ujson_t *uj) {
  extclk_sca_fi_subcommand_t cmd;
  TRY(ujson_deserialize_extclk_sca_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kExtClkScaFiSubcommandConfigure:
      return handle_extclk_sca_fi_configure(uj);
    default:
      LOG_ERROR("Unrecognized EXTCLK SCA FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
