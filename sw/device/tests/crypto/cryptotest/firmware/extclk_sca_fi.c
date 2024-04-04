// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/extclk_sca_fi.h"

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/extclk_sca_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_clkmgr_t clkmgr;

status_t handle_extclk_sca_fi_configure(ujson_t *uj) {
  cryptotest_extclk_sca_fi_cfg_t uj_data;
  TRY(ujson_deserialize_cryptotest_extclk_sca_fi_cfg_t(uj, &uj_data));

  TRY(dif_clkmgr_init(mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR),
                      &clkmgr));

  multi_bit_bool_t is_low_speed = kMultiBitBool4True;
  if (uj_data.hi_speed_sel) {
    is_low_speed = kMultiBitBool4False;
  }

  if (uj_data.sel) {
    // Enable external clock.
    TRY(dif_clkmgr_external_clock_set_enabled(&clkmgr, is_low_speed));
  } else {
    // Disable external clock.
    TRY(dif_clkmgr_external_clock_set_disabled(&clkmgr));
  }
  // Check CLKMGR_EXTCLK_STATUS_REG_OFFSET register. Blocks if clock does not
  // switch.
  TRY(dif_clkmgr_wait_for_ext_clk_switch(&clkmgr));

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
