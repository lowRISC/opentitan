// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
   PATTGEN IOS test
   The test programs both channels of the pattgen to random patterns.
   Pattgen ios are connected as follows:
   pda_tx[0] - IOB9
   pcl_tx[0] - IOB10
   pda_tx[1] - IOB11
   pcl_tx[1] - IOB12

   The random pattern programmed by 'chip_sw_patt_ios_vseq.sv'
   and output will be collected at the PADS and compared in SV test bench.
 */

OTTF_DEFINE_TEST_CONFIG();

// Following volatile const will be overwritten by
// SV testbench with random values.
// 1: channel 0, 2: channel 1, 3: Both channels
static volatile const uint8_t kChannelEnable = 3;

static volatile const uint8_t kPattPol0 = kDifPattgenPolarityLow;
static volatile const uint32_t kPattDiv0 = 0;
static volatile const uint32_t kPattLower0 = 0x76543210;
static volatile const uint32_t kPattUpper0 = 0x76543210;
static volatile const uint8_t kPattLen0 = 40;
static volatile const uint16_t kPattRep0 = 3;

static volatile const uint8_t kPattPol1 = kDifPattgenPolarityLow;
static volatile const uint32_t kPattDiv1 = 0;
static volatile const uint32_t kPattLower1 = 0x76543210;
static volatile const uint32_t kPattUpper1 = 0x76543210;
static volatile const uint8_t kPattLen1 = 40;
static volatile const uint16_t kPattRep1 = 3;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static const uint8_t kPattOuts = 4;

static const dif_pinmux_index_t kPinmuxOutsel[] = {
    kTopEarlgreyPinmuxOutselPattgenPda0Tx, /**< = 49: Peripheral Output 46 */
    kTopEarlgreyPinmuxOutselPattgenPcl0Tx, /**< = 50: Peripheral Output 47 */
    kTopEarlgreyPinmuxOutselPattgenPda1Tx, /**< = 51: Peripheral Output 48 */
    kTopEarlgreyPinmuxOutselPattgenPcl1Tx, /**< = 52: Peripheral Output 49 */
};
static const dif_pinmux_index_t kPinmuxMioOut[] = {
    kTopEarlgreyPinmuxMioOutIob9,   // pda0_tx
    kTopEarlgreyPinmuxMioOutIob10,  // pcl0_tx
    kTopEarlgreyPinmuxMioOutIob11,  // pda1_tx
    kTopEarlgreyPinmuxMioOutIob12,  // pcl1_tx
};

static dif_rv_plic_t plic;
static dif_pattgen_t pattgen;

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t irq_id;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));
  LOG_INFO("IRQ detected %0d", irq_id);

  switch (irq_id) {
    case kTopEarlgreyPlicIrqIdPattgenDoneCh0:
      LOG_INFO("Channel 0");
      break;
    case kTopEarlgreyPlicIrqIdPattgenDoneCh1:
      LOG_INFO("Channel 1");
      break;
    default:
      LOG_FATAL("IRQ: unknown irq %d", irq_id);
      break;
  }
}

bool test_main(void) {
  dif_pinmux_t pinmux;

  // Disable irq_global_ctrl to avoid the race condition between
  // `wait_for_interrupt` and OTTF interrupt handling.
  irq_global_ctrl(/*en=*/false);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pattgen_init(
      mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR), &pattgen));
  CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel0,
                                               kDifToggleDisabled));
  CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel1,
                                               kDifToggleDisabled));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdPattgenDoneCh0,
                                     kTopEarlgreyPlicIrqIdPattgenDoneCh1);

  // Initialize pinmux
  // Assign PattgenOutput to IOB9..12
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  LOG_INFO("pinmux_init begin");
  for (uint8_t i = 0; i < kPattOuts; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, kPinmuxMioOut[i], kPinmuxOutsel[i]));
  }
  // Do not remove below msg.
  LOG_INFO("pinmux_init end");

  // Enable pattgen interrupt at plic
  CHECK_DIF_OK(dif_pattgen_irq_set_enabled(&pattgen, kDifPattgenIrqDoneCh0,
                                           kDifToggleEnabled));
  CHECK_DIF_OK(dif_pattgen_irq_set_enabled(&pattgen, kDifPattgenIrqDoneCh1,
                                           kDifToggleEnabled));

  // Program pattgen if the channel is enabled.
  dif_pattgen_channel_config_t patt_cfg;
  if (kChannelEnable & 0x1) {
    patt_cfg.polarity = kPattPol0;
    patt_cfg.clock_divisor = kPattDiv0;
    patt_cfg.seed_pattern_lower_word = kPattLower0;
    patt_cfg.seed_pattern_upper_word = kPattUpper0;
    patt_cfg.seed_pattern_length = kPattLen0;
    patt_cfg.num_pattern_repetitions = kPattRep0;
    CHECK_DIF_OK(
        dif_pattgen_configure_channel(&pattgen, kDifPattgenChannel0, patt_cfg));

    LOG_INFO("TEST CH0 Enable");
    CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel0,
                                                 kDifToggleEnabled));
  }

  if (kChannelEnable & 0x2) {
    patt_cfg.polarity = kPattPol1;
    patt_cfg.clock_divisor = kPattDiv1;
    patt_cfg.seed_pattern_lower_word = kPattLower1;
    patt_cfg.seed_pattern_upper_word = kPattUpper1;
    patt_cfg.seed_pattern_length = kPattLen1;
    patt_cfg.num_pattern_repetitions = kPattRep1;
    CHECK_DIF_OK(
        dif_pattgen_configure_channel(&pattgen, kDifPattgenChannel1, patt_cfg));

    LOG_INFO("TEST CH1 Enable");
    CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel1,
                                                 kDifToggleEnabled));
  }

  LOG_INFO("Wait for interrupt");
  wait_for_interrupt();

  // Enable irq_global_ctrl to let OTTF handle interrupt.
  irq_global_ctrl(/*en=*/true);

  // Make sure both interrupts are triggered when both channels are enabled.
  // Because interrupt from each channel can be triggered at different time,
  // 'wait_for_interrupt' is not sufficient
  uint32_t state = 0;
  while (state != kChannelEnable) {
    CHECK_DIF_OK(dif_pattgen_irq_get_state(&pattgen, &state));
  }

  // Check the expected interrupt is triggered.
  bool is_pending;
  if (kChannelEnable & 0x1) {
    CHECK_DIF_OK(dif_pattgen_irq_is_pending(&pattgen, kDifPattgenIrqDoneCh0,
                                            &is_pending));
    CHECK(is_pending == true);
    CHECK_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen, kDifPattgenIrqDoneCh0));
  }

  if (kChannelEnable & 0x2) {
    CHECK_DIF_OK(dif_pattgen_irq_is_pending(&pattgen, kDifPattgenIrqDoneCh1,
                                            &is_pending));
    CHECK(is_pending == true);
    CHECK_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen, kDifPattgenIrqDoneCh1));
  }

  // Do not remove the below message
  LOG_INFO("TEST DONE");
  return true;
}
