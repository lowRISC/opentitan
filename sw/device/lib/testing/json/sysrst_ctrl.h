// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SYSRST_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SYSRST_CTRL_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

// Note: these values match the ones of `dif_sysrst_ctrl_pin_t` in
// `sw/device/lib/dif/sysrst_ctrl.h`.
#define ENUM_SYSRST_CTRL_PIN(_, value) \
    value(_, Key0In, 1 << 0) \
    value(_, Key0Out, 1 << 1) \
    value(_, Key1In, 1 << 2) \
    value(_, Key1Out, 1 << 3) \
    value(_, Key2In, 1 << 4) \
    value(_, Key2Out, 1 << 5) \
    value(_, PowerButtonIn, 1 << 6) \
    value(_, PowerButtonOut, 1 << 7) \
    value(_, AcPowerPresentIn, 1 << 8) \
    value(_, BatteryDisableOut, 1 << 9) \
    value(_, LidOpenIn, 1 << 10) \
    value(_, Z3WakeupOut, 1 << 11) \
    value(_, EcResetInOut, 1 << 12) \
    value(_, FlashWriteProtectInOut, 1 << 13)
UJSON_SERDE_ENUM(SysrstCtrlPin, sysrst_ctrl_pin_t, ENUM_SYSRST_CTRL_PIN);

// See `dif_sysrst_ctrl_pin_config_t` in `sw/device/lib/dif/sysrst_ctrl.h`
// for documentation.
#define STRUCT_SYSRST_CTRL_PIN_CONFIG(field, string) \
    field(pin, sysrst_ctrl_pin_t) \
    field(enabled, bool) \
    field(allow_zero, bool) \
    field(allow_one, bool) \
    field(override_value, bool)
UJSON_SERDE_STRUCT(SysrstCtrlPinConfig, sysrst_ctrl_pin_config_t,
                   STRUCT_SYSRST_CTRL_PIN_CONFIG);

#define ENUM_SYSRST_CTRL_COMMAND(_, value) \
    /* followed by SysrstCtrlPin, returns a bool */ \
    value(_, ReadPin) \
    /* followed by SysrstCtrlPinConfig, returns a status_t */ \
    value(_, ConfigurePinOverride)
UJSON_SERDE_ENUM(SysrstCtrlCommand, sysrst_ctrl_command_t,
                 ENUM_SYSRST_CTRL_COMMAND);

// clang-format on

#ifndef RUST_PREPROCESSOR_EMIT
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
/**
 * Process a sysrst ctrl command.
 */
status_t sysrst_ctrl_command(ujson_t *uj, dif_sysrst_ctrl_t *pinmux);
#endif  // RUST_PREPROCESSOR_EMIT
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SYSRST_CTRL_H_
