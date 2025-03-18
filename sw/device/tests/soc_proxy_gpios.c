// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_soc_proxy.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_pinmux_t pinmux;
  dif_rv_plic_t rv_plic;
  dif_soc_proxy_t soc_proxy;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_DARJEELING_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR), &rv_plic));
  CHECK_DIF_OK(dif_soc_proxy_init(
      mmio_region_from_addr(TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR),
      &soc_proxy));

  // Enable external IRQs in Ibex.
  irq_external_ctrl(true);

  // Enable IRQ0 in SoC Proxy and PLIC.
  const dif_soc_proxy_irq_t soc_proxy_irq = 0;
  const dif_rv_plic_irq_id_t rv_plic_irq =
      kTopDarjeelingPlicIrqIdSocProxyExternal0;
  const dif_rv_plic_target_t rv_plic_target = kTopDarjeelingPlicTargetIbex0;
  CHECK_DIF_OK(dif_soc_proxy_irq_set_enabled(&soc_proxy, soc_proxy_irq,
                                             kDifToggleEnabled));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, rv_plic_irq, 1));
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, rv_plic_irq,
                                           rv_plic_target, kDifToggleEnabled));

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

  // Wait for interrupt through which DV signals the switch to muxable GPOs.
  unsigned try_num = 0;
  while (true) {
    if (try_num > 10) {
      LOG_ERROR("Exceeded allowed number of unexpected IRQs!");
      return false;
    }

    wait_for_interrupt();
    bool soc_proxy_irq_pending, rv_plic_irq_pending;
    CHECK_DIF_OK(dif_soc_proxy_irq_is_pending(&soc_proxy, soc_proxy_irq,
                                              &soc_proxy_irq_pending));
    CHECK_DIF_OK(dif_rv_plic_irq_is_pending(&rv_plic, rv_plic_irq,
                                            &rv_plic_irq_pending));
    if (soc_proxy_irq_pending && rv_plic_irq_pending) {
      break;
    }

    try_num++;
  }

  // Acknowledge and complete IRQ.
  CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge(&soc_proxy, soc_proxy_irq));
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, rv_plic_target, rv_plic_irq));

  // Disable IRQ in PLIC and SoC Proxy.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, rv_plic_irq,
                                           rv_plic_target, kDifToggleDisabled));
  CHECK_DIF_OK(dif_soc_proxy_irq_set_enabled(&soc_proxy, soc_proxy_irq,
                                             kDifToggleDisabled));

  // Disable external IRQs in Ibex.
  irq_external_ctrl(false);

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
