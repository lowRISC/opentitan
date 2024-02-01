// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/* We need control flow for the ujson messages exchanged
 * with the host in OTTF_WAIT_FOR on real devices. */
OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_rv_plic_t plic;

enum {
  kCurrentTestPhaseTimeoutUsecDV = 20,
  kCurrentTestPhaseTimeoutUsecReal = 1000000,
  kPlicTarget = kTopEarlgreyPlicTargetIbex0,
};

static volatile bool irq_triggered;

// On DV, we must use variables in flash.
// On a real device, we must use variables in RAM.
// In DV, the sequence can ensure that the pins are set even before the test
// runs. On a real device, this is not the case and if the initial value of
// kCurrentTestPhaseReal is 0, the very first OTTF_WAIT_FOR could succeed before
// the host can set the pins. To avoid this, and only on real devices, set the
// initial value to an invalid value so that we have to wait for the host.
static volatile const uint8_t kCurrentTestPhaseDV = 0;
static volatile uint8_t kCurrentTestPhaseReal = 0xff;
uint8_t phase = 0;

enum {
  kOutputNumPads = 0x8,
  kOutputNumMioPads = 0x6,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
};

static const dif_pinmux_index_t kInputPadsDV[] = {
    kTopEarlgreyPinmuxInselIob3, kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob8, kTopEarlgreyPinmuxInselIor13,
    kTopEarlgreyPinmuxInselIoc7, kTopEarlgreyPinmuxInselIoc9,
};

// We need different pins on the hyperdebug boards since certain
// pins are not routed to the hyperdebug.
static const dif_pinmux_index_t kInputPadsReal[] = {
    kTopEarlgreyPinmuxInselIor10, kTopEarlgreyPinmuxInselIor11,
    kTopEarlgreyPinmuxInselIor12, kTopEarlgreyPinmuxInselIor5,
    kTopEarlgreyPinmuxInselIor6,  kTopEarlgreyPinmuxInselIor7,
};

void test_phase_sync(void) {
  test_status_set(kTestStatusInTest);
  test_status_set(kTestStatusInWfi);
}

/**
 * Configure for input change detection, sync with DV side, wait for input
 * change interrupt, check the interrupt cause and clear it.
 */
void sysrst_ctrl_input_change_detect(
    dif_sysrst_ctrl_key_intr_src_t expected_key_intr_src) {
  const uint32_t kCurrentTestPhaseTimeoutUsec =
      kDeviceType == kDeviceSimDV ? kCurrentTestPhaseTimeoutUsecDV
                                  : kCurrentTestPhaseTimeoutUsecReal;
  const volatile uint8_t *kCurrentTestPhase = kDeviceType == kDeviceSimDV
                                                  ? &kCurrentTestPhaseDV
                                                  : &kCurrentTestPhaseReal;

  irq_triggered = false;
  LOG_INFO("Wait for test to start: want phase %d", phase);
  OTTF_WAIT_FOR(phase == *kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  phase++;
  LOG_INFO("Setup sysrst_ctrl");

  // Configure for input change.
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = (dif_sysrst_ctrl_input_change_t)expected_key_intr_src,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));

  // Enable sysrst ctrl irq.
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlIrqEventDetected, kDifToggleEnabled));

  LOG_INFO("Tell host we are ready");
  test_phase_sync();

  OTTF_WAIT_FOR(phase == *kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  phase++;
  // Check that the interrupt isn't triggered at the first part of the test.
  CHECK(!irq_triggered, "The interrupt is triggered during input glitch.");
  LOG_INFO("Tell host we did not detect the glitch");
  test_phase_sync();

  ATOMIC_WAIT_FOR_INTERRUPT(irq_triggered);

  uint32_t causes;
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_irq_get_causes(&sysrst_ctrl, &causes));
  CHECK(causes == expected_key_intr_src, "Intr cause do not match: %d vs %d!",
        causes, (int)expected_key_intr_src);

  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_irq_clear_causes(&sysrst_ctrl, causes));

  // Reset configuration for input change.
  config.input_changes = 0;
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));

  // Tell host to finish the test (only on real devices).
  LOG_INFO("Tell host to finish the test");
  if (kDeviceType != kDeviceSimDV)
    test_phase_sync();
}

/**
 * Configure for key combo change detection, sync with DV side, wait for input
 * change interrupt, check the interrupt cause and clear it.
 */
void sysrst_ctrl_key_combo_detect(dif_sysrst_ctrl_key_combo_t key_combo,
                                  uint32_t combo_keys) {
  const uint32_t kCurrentTestPhaseTimeoutUsec =
      kDeviceType == kDeviceSimDV ? kCurrentTestPhaseTimeoutUsecDV
                                  : kCurrentTestPhaseTimeoutUsecReal;
  const volatile uint8_t *kCurrentTestPhase = kDeviceType == kDeviceSimDV
                                                  ? &kCurrentTestPhaseDV
                                                  : &kCurrentTestPhaseReal;

  irq_triggered = false;
  LOG_INFO("wait for test to start");
  OTTF_WAIT_FOR(phase == *kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  phase++;
  LOG_INFO("configure sysrst interrupt");

  // Configure for key combo
  dif_sysrst_ctrl_key_combo_config_t sysrst_ctrl_key_combo_config = {
      .keys = combo_keys,
      .detection_time_threshold = 1,
      .actions = kDifSysrstCtrlKeyComboActionInterrupt,
      .embedded_controller_reset_duration = 1,
  };
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, key_combo, sysrst_ctrl_key_combo_config));

  // Enable sysrst ctrl irq.
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlIrqEventDetected, kDifToggleEnabled));

  LOG_INFO("tell host we are ready");
  test_phase_sync();

  OTTF_WAIT_FOR(phase == *kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  phase++;
  // Check that the interrupt isn't triggered at the first part of the test.
  CHECK(!irq_triggered, "The interrupt is triggered during input glitch.");
  LOG_INFO("tell host we did not detect the glitch");
  test_phase_sync();

  LOG_INFO("wait for interrupt");
  ATOMIC_WAIT_FOR_INTERRUPT(irq_triggered);
  LOG_INFO("interrupt triggered, checks causes");

  uint32_t causes;
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_irq_get_causes(&sysrst_ctrl, &causes));
  CHECK(causes == key_combo, "Intr cause do not match: %d vs %d!", causes,
        (int)key_combo);

  CHECK_DIF_OK(
      dif_sysrst_ctrl_key_combo_irq_clear_causes(&sysrst_ctrl, causes));

  // Reset configuration for key combo.
  sysrst_ctrl_key_combo_config.keys = 0;
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, key_combo, sysrst_ctrl_key_combo_config));

  // Tell host to finish the test (only on real devices).
  LOG_INFO("Tell host to finish the test");
  if (kDeviceType != kDeviceSimDV)
    test_phase_sync();
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
  dif_rv_plic_irq_id_t plic_irq_id = 0;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralUart0:
      if (!ottf_console_flow_control_isr(exc_info)) {
        goto unexpected_irq;
      };
      break;
    case kTopEarlgreyPlicPeripheralSysrstCtrlAon: {
      // Check that the ID matches the expected interrupt, then mask it, since
      // it's a status type.
      dif_sysrst_ctrl_irq_t irq =
          (dif_sysrst_ctrl_irq_t)(plic_irq_id -
                                  (dif_rv_plic_irq_id_t)
                                      kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected);
      CHECK(irq == kDifSysrstCtrlIrqEventDetected);
      CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(&sysrst_ctrl, irq,
                                                   kDifToggleDisabled));
      irq_triggered = true;
    } break;
    default:
      goto unexpected_irq;
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, plic_irq_id));
  return;

  // A label to jump to for common error handling.
unexpected_irq:
  CHECK(false, "Unexpected external IRQ %d", plic_irq_id);
}

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic));

  // Enable all the SYSRST CTRL interrupts on PLIC.
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected,
      kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected);

  // Initialize sysrst ctrl.
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));

  // Set input pins.
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  // On real devices, we also need to configure the DIO pins.
  if (kDeviceType != kDeviceSimDV) {
    sysrst_ctrl_testutils_setup_dio(&pinmux);
    // Release pins so the host can control them.
    sysrst_ctrl_testutils_release_dio(&sysrst_ctrl, true, true);
    // Disable the EC reset pulse so that it does not interfere with the test.
    sysrst_ctrl_testutils_set_ec_rst_pulse_width(&sysrst_ctrl, 0);
  }
  const dif_pinmux_index_t *kInputPads =
      kDeviceType == kDeviceSimDV ? kInputPadsDV : kInputPadsReal;
  for (int i = 0; i < kOutputNumMioPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }

  // Test 14 different input transition. 7 L2H and 7 H2L input transition.
  for (dif_sysrst_ctrl_key_intr_src_t i =
           kDifSysrstCtrlKeyIntrStatusInputPowerButtonH2L;
       i <= kDifSysrstCtrlKeyIntrStatusInputFlashWriteProtectL2H; i = i << 1) {
    sysrst_ctrl_input_change_detect(i);
  }

  // Test 4 different combo key intr sources with 2, 3, 4 and 5 combo key
  // transition H2L.
  uint32_t combo_keys_0 = kDifSysrstCtrlKeyPowerButton | kDifSysrstCtrlKey0;
  sysrst_ctrl_key_combo_detect(kDifSysrstCtrlKeyCombo0, combo_keys_0);

  uint32_t combo_keys_1 =
      kDifSysrstCtrlKey1 | kDifSysrstCtrlKey2 | kDifSysrstCtrlKeyAcPowerPresent;
  sysrst_ctrl_key_combo_detect(kDifSysrstCtrlKeyCombo1, combo_keys_1);

  uint32_t combo_keys_2 = kDifSysrstCtrlKeyPowerButton | kDifSysrstCtrlKey0 |
                          kDifSysrstCtrlKey2 | kDifSysrstCtrlKeyAcPowerPresent;
  sysrst_ctrl_key_combo_detect(kDifSysrstCtrlKeyCombo2, combo_keys_2);

  uint32_t combo_keys_3 = kDifSysrstCtrlKeyPowerButton | kDifSysrstCtrlKey0 |
                          kDifSysrstCtrlKey1 | kDifSysrstCtrlKey2 |
                          kDifSysrstCtrlKeyAcPowerPresent;
  sysrst_ctrl_key_combo_detect(kDifSysrstCtrlKeyCombo3, combo_keys_3);

  // Last sync with dv side.
  test_status_set(kTestStatusInTest);
  return true;
}
