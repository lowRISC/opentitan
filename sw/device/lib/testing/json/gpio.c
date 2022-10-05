// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/testing/json/gpio.h"

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

status_t gpio_set(ujson_t *uj, const dif_gpio_t *gpio) {
  gpio_set_t op;
  TRY(ujson_deserialize_gpio_set_t(uj, &op));
  switch (op.action) {
    case kGpioActionWrite:
      TRY(dif_gpio_write(gpio, (dif_gpio_pin_t)op.pin_mask, (bool)op.state));
      break;
    case kGpioActionWriteAll:
      TRY(dif_gpio_write_all(gpio, (dif_gpio_state_t)op.state));
      break;
    case kGpioActionWriteMasked:
      TRY(dif_gpio_write_masked(gpio, (dif_gpio_mask_t)op.pin_mask,
                                (dif_gpio_state_t)op.state));
      break;
    case kGpioActionSetEnabled:
      TRY(dif_gpio_output_set_enabled(gpio, (dif_gpio_pin_t)op.pin_mask,
                                      (dif_toggle_t)op.state));
      break;
    case kGpioActionSetEnabledAll:
      TRY(dif_gpio_output_set_enabled_all(gpio, (dif_gpio_state_t)op.state));
      break;
    case kGpioActionSetEnabledMasked:
      TRY(dif_gpio_output_set_enabled_masked(gpio, (dif_gpio_mask_t)op.pin_mask,
                                             (dif_gpio_state_t)op.state));
      break;
    case kGpioActionSetInputNoiseFilter:
      TRY(dif_gpio_input_noise_filter_set_enabled(
          gpio, (dif_gpio_mask_t)op.pin_mask, (dif_gpio_state_t)op.state));
      break;
    default:
      return INVALID_ARGUMENT();
  }
  return RESP_OK_STATUS(uj);
}

status_t gpio_get(ujson_t *uj, const dif_gpio_t *gpio) {
  dif_gpio_state_t state;
  TRY(dif_gpio_read_all(gpio, &state));
  gpio_get_t val = {state};
  return RESP_OK(ujson_serialize_gpio_get_t, uj, &val);
}
