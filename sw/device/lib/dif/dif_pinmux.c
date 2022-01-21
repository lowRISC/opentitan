// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/dif/dif_base.h"

#include "pinmux_regs.h"  // Generated.

// This just exists to check that the header compiles for now. The actual
// implementation is work in progress.

OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_input_select(const dif_pinmux_t *pinmux,
                                     dif_pinmux_index_t peripheral_input,
                                     dif_pinmux_index_t insel) {
  if (pinmux == NULL || peripheral_input >= PINMUX_PARAM_N_MIO_PERIPH_IN ||
      insel >= (2 + PINMUX_PARAM_N_MIO_PADS)) {
    return kDifBadArg;
  }
  uint32_t reg_offset =
      PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET + (peripheral_input << 2);
  uint32_t reg_value =
      bitfield_field32_write(0, PINMUX_MIO_PERIPH_INSEL_0_IN_0_FIELD, insel);
  mmio_region_write32(pinmux->base_addr, reg_offset, reg_value);
  return kDifOk;
}
