// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pattgen_regs.h"  // Generated.

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

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kTestCmdTimeoutUsec = 5000000,
};

/* Macro to define and use variable that need to be stored in flash
 * for DV tests and RAM for real tests, to enable backdoor access. */
#define DEFINE_BACKDOOR_VAR(type, name, default_val)                       \
  /* DV variable in flash. */                                              \
  OT_SECTION(".rodata") static volatile const type name##DV = default_val; \
  /* non-DV variable in RAM. */                                            \
  OT_SECTION(".data") type name##Real = default_val;

#define BACKDOOR_VAR(name) (kDeviceType == kDeviceSimDV ? name##DV : name##Real)

// Following volatile const will be overwritten by
// SV testbench with random values.
// 1: channel 0, 2: channel 1, 3: Both channels
DEFINE_BACKDOOR_VAR(uint8_t, kChannelEnable, 3)

DEFINE_BACKDOOR_VAR(uint8_t, kPattPol0, kDifPattgenPolarityLow)
DEFINE_BACKDOOR_VAR(uint32_t, kPattDiv0, 0)
DEFINE_BACKDOOR_VAR(uint32_t, kPattLower0, 0x76543210)
DEFINE_BACKDOOR_VAR(uint32_t, kPattUpper0, 0x76543210)
DEFINE_BACKDOOR_VAR(uint8_t, kPattLen0, 40)
DEFINE_BACKDOOR_VAR(uint16_t, kPattRep0, 3)

DEFINE_BACKDOOR_VAR(uint8_t, kPattPol1, kDifPattgenPolarityLow)
DEFINE_BACKDOOR_VAR(uint32_t, kPattDiv1, 0)
DEFINE_BACKDOOR_VAR(uint32_t, kPattLower1, 0x76543210)
DEFINE_BACKDOOR_VAR(uint32_t, kPattUpper1, 0x76543210)
DEFINE_BACKDOOR_VAR(uint8_t, kPattLen1, 40)
DEFINE_BACKDOOR_VAR(uint16_t, kPattRep1, 3)

typedef enum {
  kTestCmdWait = 0,
  kTestCmdConfigure = 1,
  kTestCmdRun = 2,
  kTestCmdStop = 3,
} test_cmd_t;

/* Backdoor variable for real device */
uint8_t test_cmd = kTestCmdWait;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static const uint8_t kPattOuts = 4;

static const dif_pinmux_index_t kPinmuxOutsel[] = {
    kTopEarlgreyPinmuxOutselPattgenPda0Tx, /**< = 49: Peripheral Output 46 */
    kTopEarlgreyPinmuxOutselPattgenPcl0Tx, /**< = 50: Peripheral Output 47 */
    kTopEarlgreyPinmuxOutselPattgenPda1Tx, /**< = 51: Peripheral Output 48 */
    kTopEarlgreyPinmuxOutselPattgenPcl1Tx, /**< = 52: Peripheral Output 49 */
};
static const dif_pinmux_index_t kPinmuxMioOutDV[] = {
    kTopEarlgreyPinmuxMioOutIob9,   // pda0_tx
    kTopEarlgreyPinmuxMioOutIob10,  // pcl0_tx
    kTopEarlgreyPinmuxMioOutIob11,  // pda1_tx
    kTopEarlgreyPinmuxMioOutIob12,  // pcl1_tx
};
static const dif_pinmux_index_t kPinmuxMioOutReal[] = {
    kTopEarlgreyPinmuxMioOutIor10,  // pda0_tx
    kTopEarlgreyPinmuxMioOutIor11,  // pcl0_tx
    kTopEarlgreyPinmuxMioOutIor12,  // pda1_tx
    kTopEarlgreyPinmuxMioOutIor13,  // pcl1_tx
};

static dif_rv_plic_t plic;
static dif_pattgen_t pattgen;
static volatile uint8_t channel_fired = 0;

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t irq_id;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));
  // Handle OTTF interrupt.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];
  if (peripheral == kTopEarlgreyPlicPeripheralUart0 &&
      ottf_console_flow_control_isr(exc_info)) {
    return;
  }

  LOG_INFO("IRQ detected %d", irq_id);

  bool is_pending;
  switch (irq_id) {
    case kTopEarlgreyPlicIrqIdPattgenDoneCh0:
      LOG_INFO("Channel 0");
      channel_fired |= 1 << 0;
      // Check the expected interrupt is triggered.
      CHECK_DIF_OK(dif_pattgen_irq_is_pending(&pattgen, kDifPattgenIrqDoneCh0,
                                              &is_pending));
      CHECK(is_pending == true);
      CHECK_DIF_OK(
          dif_pattgen_irq_acknowledge(&pattgen, kDifPattgenIrqDoneCh0));
      break;
    case kTopEarlgreyPlicIrqIdPattgenDoneCh1:
      channel_fired |= 1 << 1;
      LOG_INFO("Channel 1");
      // Check the expected interrupt is triggered.
      CHECK_DIF_OK(dif_pattgen_irq_is_pending(&pattgen, kDifPattgenIrqDoneCh1,
                                              &is_pending));
      CHECK(is_pending == true);
      CHECK_DIF_OK(
          dif_pattgen_irq_acknowledge(&pattgen, kDifPattgenIrqDoneCh1));
      break;
    default:
      LOG_FATAL("IRQ: unknown irq %d", irq_id);
      break;
  }
  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

static void run_test(void);

bool test_main(void) {
  dif_pinmux_t pinmux;
  // Let the host know the peripheral frequency.
  LOG_INFO("peripheral frequency: %u", (unsigned int)kClockFreqPeripheralHz);

  irq_global_ctrl(true);
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
  const dif_pinmux_index_t *kPinmuxMioOut =
      kDeviceType == kDeviceSimDV ? kPinmuxMioOutDV : kPinmuxMioOutReal;
  for (uint8_t i = 0; i < kPattOuts; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, kPinmuxMioOut[i], kPinmuxOutsel[i]));
  }
  // Do not remove below msg.
  LOG_INFO("pinmux_init end");

  // In DV, we only run the test once.
  if (kDeviceType == kDeviceSimDV) {
    run_test();
    return true;
  }
  // On FPGA/silicon, we run the test in a loop.
  while (true) {
    test_cmd = kTestCmdWait;
    OTTF_WAIT_FOR(test_cmd != kTestCmdWait, kTestCmdTimeoutUsec);
    if (test_cmd == kTestCmdStop) {
      break;
    }
    CHECK(test_cmd == kTestCmdConfigure);
    run_test();
  }
  return true;
}

static void run_test(void) {
  // Enable pattgen interrupt at plic
  CHECK_DIF_OK(dif_pattgen_irq_set_enabled(&pattgen, kDifPattgenIrqDoneCh0,
                                           kDifToggleEnabled));
  CHECK_DIF_OK(dif_pattgen_irq_set_enabled(&pattgen, kDifPattgenIrqDoneCh1,
                                           kDifToggleEnabled));

  channel_fired = 0;
  // Program pattgen if the channel is enabled.
  dif_pattgen_channel_config_t patt_cfg;
  if (BACKDOOR_VAR(kChannelEnable) & 0x1) {
    patt_cfg.polarity = BACKDOOR_VAR(kPattPol0);
    patt_cfg.clock_divisor = BACKDOOR_VAR(kPattDiv0);
    patt_cfg.seed_pattern_lower_word = BACKDOOR_VAR(kPattLower0);
    patt_cfg.seed_pattern_upper_word = BACKDOOR_VAR(kPattUpper0);
    patt_cfg.seed_pattern_length = BACKDOOR_VAR(kPattLen0);
    patt_cfg.num_pattern_repetitions = BACKDOOR_VAR(kPattRep0);
    CHECK_DIF_OK(
        dif_pattgen_configure_channel(&pattgen, kDifPattgenChannel0, patt_cfg));
  }

  if (BACKDOOR_VAR(kChannelEnable) & 0x2) {
    patt_cfg.polarity = BACKDOOR_VAR(kPattPol1);
    patt_cfg.clock_divisor = BACKDOOR_VAR(kPattDiv1);
    patt_cfg.seed_pattern_lower_word = BACKDOOR_VAR(kPattLower1);
    patt_cfg.seed_pattern_upper_word = BACKDOOR_VAR(kPattUpper1);
    patt_cfg.seed_pattern_length = BACKDOOR_VAR(kPattLen1);
    patt_cfg.num_pattern_repetitions = BACKDOOR_VAR(kPattRep1);
    CHECK_DIF_OK(
        dif_pattgen_configure_channel(&pattgen, kDifPattgenChannel1, patt_cfg));
  }
  // Tell host that the channels are configured.
  LOG_INFO("Channels configured");
  // Wait for host to tell us to run.
  if (kDeviceType != kDeviceSimDV) {
    OTTF_WAIT_FOR(test_cmd == kTestCmdRun, kTestCmdTimeoutUsec);
  }

  // Start channels.
  if (BACKDOOR_VAR(kChannelEnable) & 0x1) {
    CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel0,
                                                 kDifToggleEnabled));
  }
  if (BACKDOOR_VAR(kChannelEnable) & 0x2) {
    CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel1,
                                                 kDifToggleEnabled));
  }

  // Make sure both interrupts are triggered when both channels are enabled.
  // Because interrupt from each channel can be triggered at different time,
  // 'wait_for_interrupt' is not sufficient
  ATOMIC_WAIT_FOR_INTERRUPT(channel_fired == BACKDOOR_VAR(kChannelEnable));

  // Disable both channels.
  CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel0,
                                               kDifToggleDisabled));
  CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, kDifPattgenChannel1,
                                               kDifToggleDisabled));

  // Do not remove the below message
  LOG_INFO("TEST DONE");
}
