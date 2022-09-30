// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_GPIO_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_GPIO_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define ENUM_GPIO_SET_ACTION(_, value) \
    value(_, Write) \
    value(_, WriteAll) \
    value(_, WriteMasked) \
    value(_, SetEnabled) \
    value(_, SetEnabledAll) \
    value(_, SetEnabledMasked) \
    value(_, SetInputNoiseFilter)
UJSON_SERDE_ENUM(GpioAction, gpio_action_t, ENUM_GPIO_SET_ACTION);

#define STRUCT_GPIO_SET(field, string) \
    field(action, gpio_action_t) \
    field(pin_mask, uint32_t) \
    field(state, uint32_t)
UJSON_SERDE_STRUCT(GpioSet, gpio_set_t, STRUCT_GPIO_SET);

#define STRUCT_GPIO_GET(field, string) \
    field(state, uint32_t)
UJSON_SERDE_STRUCT(GpioGet, gpio_get_t, STRUCT_GPIO_GET);

#ifndef RUST_PREPROCESSOR_EMIT
#include "sw/device/lib/dif/dif_gpio.h"

status_t gpio_set(ujson_t *uj, const dif_gpio_t *gpio);
status_t gpio_get(ujson_t *uj, const dif_gpio_t *gpio);
#endif

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_GPIO_H_
