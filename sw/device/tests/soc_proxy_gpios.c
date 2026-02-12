// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_soc_proxy.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_pinmux_t pinmux;

  // Map muxable SoC GPIs in pinmux.
  top_darjeeling_pinmux_peripheral_in_t peripheral_in[] = {
      kTopDarjeelingPinmuxPeripheralInSocProxySocGpi12,
      kTopDarjeelingPinmuxPeripheralInSocProxySocGpi13,
      kTopDarjeelingPinmuxPeripheralInSocProxySocGpi14,
      kTopDarjeelingPinmuxPeripheralInSocProxySocGpi15,
  };
  top_darjeeling_pinmux_insel_t insel[] = {
      kTopDarjeelingPinmuxInselMio4,
      kTopDarjeelingPinmuxInselMio5,
      kTopDarjeelingPinmuxInselMio6,
      kTopDarjeelingPinmuxInselMio7,
  };
  static_assert(ARRAYSIZE(peripheral_in) == ARRAYSIZE(insel),
                "Illegal pinmux input configuration arrays!");
  for (size_t i = 0; i < ARRAYSIZE(peripheral_in); i++) {
    CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, peripheral_in[i], insel[i]));
  }
  LOG_INFO("Muxable SoC GPIs mapped.");

  // Map muxable SoC GPOs in pinmux.
  top_darjeeling_pinmux_mio_out_t mio_out[] = {
      kTopDarjeelingPinmuxMioOutMio4,
      kTopDarjeelingPinmuxMioOutMio5,
      kTopDarjeelingPinmuxMioOutMio6,
      kTopDarjeelingPinmuxMioOutMio7,
  };
  top_darjeeling_pinmux_outsel_t outsel[] = {
      kTopDarjeelingPinmuxOutselSocProxySocGpo12,
      kTopDarjeelingPinmuxOutselSocProxySocGpo13,
      kTopDarjeelingPinmuxOutselSocProxySocGpo14,
      kTopDarjeelingPinmuxOutselSocProxySocGpo15,
  };
  static_assert(ARRAYSIZE(mio_out) == ARRAYSIZE(outsel),
                "Illegal pinmux output configuration arrays!");
  for (size_t i = 0; i < ARRAYSIZE(mio_out); i++) {
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, mio_out[i], outsel[i]));
  }
  LOG_INFO("Muxable SoC GPOs mapped.");

  return true;
}
