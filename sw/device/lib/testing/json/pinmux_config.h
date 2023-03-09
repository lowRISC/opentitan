// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_CONFIG_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_CONFIG_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

//  Dependencies between usjon structure definitions can be a little tricky:
//  - If not generating an implementation, we can just include the dependency.
//  - If generating an implementation, we instead include the dependency in
//    the C file before setting UJSON_SERDE_IMPL.
//
//  This avoids a lot of extra preprocessor ifs, undefs and defines.
#if UJSON_SERDE_IMPL == 0
#include "sw/device/lib/testing/json/pinmux.h"
#endif
// clang-format off

#define STRUCT_PINMUX_INPUT_SELECTION(field, string) \
    field(peripheral, pinmux_peripheral_in_t, 16)    \
    field(selector, pinmux_insel_t, 16)
UJSON_SERDE_STRUCT(PinmuxInputSelection, pinmux_input_selection_t,
                   STRUCT_PINMUX_INPUT_SELECTION);

#define STRUCT_PINMUX_OUTPUT_SELECTION(field, string) \
    field(mio, pinmux_mio_out_t, 16)                  \
    field(selector, pinmux_outsel_t, 16)
UJSON_SERDE_STRUCT(PinmuxOutputSelection, pinmux_output_selection_t,
                   STRUCT_PINMUX_OUTPUT_SELECTION);

#define STRUCT_PINMUX_CONFIG(field, string) \
    field(input, pinmux_input_selection_t)  \
    field(output, pinmux_output_selection_t)
UJSON_SERDE_STRUCT(PinmuxConfig, pinmux_config_t, STRUCT_PINMUX_CONFIG);

// clang-format on
#ifndef RUST_PREPROCESSOR_EMIT
#include "sw/device/lib/dif/dif_pinmux.h"
/**
 * Configure the pinmux with a specific configuration.
 *
 * This function is specific to top_earlgrey and top_englishbreakfast.
 */
status_t pinmux_config(ujson_t *uj, dif_pinmux_t *pinmux);
#endif  // RUST_PREPROCESSOR_EMIT
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_CONFIG_H_
