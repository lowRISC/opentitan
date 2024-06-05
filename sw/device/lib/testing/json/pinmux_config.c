// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// See pinmux_config.h for the explaination of this include ordering.
#include "sw/device/lib/testing/json/pinmux.h"
#undef UJSON_SERDE_IMPL
#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/json/pinmux_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t pinmux_config(ujson_t *uj, dif_pinmux_t *pinmux) {
  pinmux_config_t config;
  TRY(ujson_deserialize_pinmux_config_t(uj, &config));

  for (size_t i = 0; i < ARRAYSIZE(config.input.peripheral); ++i) {
    if (config.input.peripheral[i] == kPinmuxPeripheralInEnd) {
      break;
    }
    TRY(dif_pinmux_input_select(pinmux, config.input.peripheral[i],
                                config.input.selector[i]));
  }
  for (size_t i = 0; i < ARRAYSIZE(config.output.mio); ++i) {
    if (config.output.mio[i] == kPinmuxMioOutEnd) {
      break;
    }
    TRY(dif_pinmux_output_select(pinmux, config.output.mio[i],
                                 config.output.selector[i]));
  }
  for (size_t i = 0; i < ARRAYSIZE(config.attrs.mio); ++i) {
    if (config.attrs.mio[i] == kPinmuxMioOutEnd) {
      break;
    }
    dif_pinmux_pad_attr_t pad_attr = {.flags = config.attrs.flags[i]};
    dif_pinmux_pad_attr_t attrs_out;
    TRY(dif_pinmux_pad_write_attrs(pinmux, config.attrs.mio[i],
                                   kDifPinmuxPadKindMio, pad_attr, &attrs_out));
  }
  return RESP_OK_STATUS(uj);
}
