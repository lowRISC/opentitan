// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/testing/json/sysrst_ctrl.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

// Convert a sysrst_ctrl_pin_t to dif_sysrst_ctrl_pin_t.
// The values were chose to be equal so that this operation is trivial.
static dif_sysrst_ctrl_pin_t pin_to_dif_pin(sysrst_ctrl_pin_t pin) {
  return (dif_sysrst_ctrl_pin_t)pin;
}

static status_t read_pin(ujson_t *uj, dif_sysrst_ctrl_t *sysrst_ctrl) {
  sysrst_ctrl_pin_t pin;
  TRY(ujson_deserialize_sysrst_ctrl_pin_t(uj, &pin));

  bool value;
  TRY(dif_sysrst_ctrl_input_pin_read(sysrst_ctrl, pin_to_dif_pin(pin), &value));

  return RESP_OK(ujson_serialize_bool, uj, &value);
}

static status_t config_pin_override(ujson_t *uj,
                                    dif_sysrst_ctrl_t *sysrst_ctrl) {
  sysrst_ctrl_pin_config_t cfg;
  TRY(ujson_deserialize_sysrst_ctrl_pin_config_t(uj, &cfg));

  dif_sysrst_ctrl_pin_config_t dif_cfg = {
      .enabled = cfg.enabled,
      .allow_zero = cfg.allow_zero,
      .allow_one = cfg.allow_one,
      .override_value = cfg.override_value,
  };
  TRY(dif_sysrst_ctrl_output_pin_override_configure(
      sysrst_ctrl, pin_to_dif_pin(cfg.pin), dif_cfg));

  return RESP_OK_STATUS(uj);
}

status_t sysrst_ctrl_command(ujson_t *uj, dif_sysrst_ctrl_t *sysrst_ctrl) {
  sysrst_ctrl_command_t command;
  TRY(ujson_deserialize_sysrst_ctrl_command_t(uj, &command));

  switch (command) {
    case kSysrstCtrlCommandReadPin:
      return read_pin(uj, sysrst_ctrl);
    case kSysrstCtrlCommandConfigurePinOverride:
      return config_pin_override(uj, sysrst_ctrl);
    default:
      RESP_ERR(uj, INVALID_ARGUMENT());
      return INVALID_ARGUMENT();
  }
}
