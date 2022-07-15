// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/sensor_ctrl_testutils.h"

#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/testing/test_framework/check.h"

bool sensor_ctrl_ast_init_done(const dif_sensor_ctrl_t *sensor_ctrl) {
  dif_toggle_t init_st = kDifToggleDisabled;
  CHECK_DIF_OK(dif_sensor_ctrl_get_ast_init_done_status(sensor_ctrl, &init_st));
  return init_st == kDifToggleEnabled;
}
