// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/pinmux.h"

#include "sw/device/lib/base/log.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_pinmux_t pinmux;

void pinmux_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR);
  if (dif_pinmux_init(base_addr, &pinmux) != kDifPinmuxInitOk) {
    LOG_FATAL("Pinmux failed to initialise");
    abort();
  }

  // Assign peripheral inputs to MIO Padring inputs (1:1, don't assign if
  // peripheral input doesn't have a pair). Try to assign consecutively
  // peripheral input 0,1,2... to MIO Padring input 0,1,2... .
  dif_pinmux_peripheral_in_t peripheral_in = 0;
  dif_pinmux_insel_t mio_in_select = kDifPinmuxInselFirstIn;
  while (peripheral_in <= kDifPinmuxPeripheralInLast &&
         mio_in_select <= kDifPinmuxInselLast) {
    dif_pinmux_result_t result =
        dif_pinmux_insel_set(&pinmux, peripheral_in, mio_in_select);
    if (result != kDifPinmuxOk) {
      LOG_FATAL("Failed to set connection: periph in (%d) and mio in (%d)",
                peripheral_in, mio_in_select);
      abort();
    }

    ++peripheral_in;
    ++mio_in_select;
  }

  // Assign peripheral outputs to MIO Padring outputs (1:1, don't assign if
  // peripheral output doesn't have a pair). Try to assign consecutively
  // peripheral output 0,1,2... to MIO Padring output 0,1,2... .
  dif_pinmux_mio_out_t mio_out = 0;
  dif_pinmux_outsel_t peripheral_out_select = kDifPinmuxOutselFirstOut;
  while (mio_out <= kDifPinmuxMioOutLast &&
         peripheral_out_select <= kDifPinmuxOutselLast) {
    dif_pinmux_result_t result =
        dif_pinmux_outsel_set(&pinmux, mio_out, peripheral_out_select);
    if (result != kDifPinmuxOk) {
      LOG_FATAL("Failed to set connection: mio out (%d) and periph out (%d)",
                mio_out, peripheral_out_select);
      abort();
    }

    ++mio_out;
    ++peripheral_out_select;
  }
}
