// Copyright lowRISC contributors.
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
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_rv_plic_t plic;

enum {
  kCurrentTestPhaseTimeoutUsec = 20,
  kPlicTarget = kTopEarlgreyPlicTargetIbex0,
};

static volatile dif_sysrst_ctrl_irq_t irq;
static volatile top_earlgrey_plic_peripheral_t peripheral;
dif_rv_plic_irq_id_t irq_id;

// Test phase written by testbench.
static volatile const uint8_t kCurrentTestPhase = 0;
uint8_t phase = 0;

enum {
  kOutputNumPads = 0x8,
  kOutputNunMioPads = 0x6,
};

static const dif_pinmux_index_t kPeripheralInputs[] = {
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
    kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
};

static const dif_pinmux_index_t kInputPads[] = {
    kTopEarlgreyPinmuxInselIob3, kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob8, kTopEarlgreyPinmuxInselIor13,
    kTopEarlgreyPinmuxInselIoc7, kTopEarlgreyPinmuxInselIoc9,
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
  peripheral = UINT32_MAX;
  IBEX_SPIN_FOR(phase++ == kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);

  // Configure for input change.
  dif_sysrst_ctrl_input_change_config_t config = {
      .input_changes = (dif_sysrst_ctrl_input_change_t)expected_key_intr_src,
      .debounce_time_threshold = 1,  // 5us
  };
  CHECK_DIF_OK(
      dif_sysrst_ctrl_input_change_detect_configure(&sysrst_ctrl, config));

  test_phase_sync();

  IBEX_SPIN_FOR(phase++ == kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  // Check that the interrupt isn't triggered at the first part of the test.
  CHECK(peripheral == UINT32_MAX,
        "The interrupt is triggered during input glitch.");
  test_phase_sync();

  wait_for_interrupt();
  // Check that the interrupt is triggered at the second part of the test.
  CHECK(peripheral == kTopEarlgreyPlicPeripheralSysrstCtrlAon,
        "The interrupt is not triggered during the test.");
  CHECK(irq_id == kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected,
        "Wrong irq_id");

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
}

/**
 * Configure for key combo change detection, sync with DV side, wait for input
 * change interrupt, check the interrupt cause and clear it.
 */
void sysrst_ctrl_key_combo_detect(dif_sysrst_ctrl_key_combo_t key_combo,
                                  uint32_t combo_keys) {
  peripheral = UINT32_MAX;
  IBEX_SPIN_FOR(phase++ == kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);

  // Configure for key combo
  dif_sysrst_ctrl_key_combo_config_t sysrst_ctrl_key_combo_config = {
      .keys = combo_keys,
      .detection_time_threshold = 1,
      .actions = kDifSysrstCtrlKeyComboActionInterrupt,
      .embedded_controller_reset_duration = 1,
  };
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, key_combo, sysrst_ctrl_key_combo_config));

  test_phase_sync();

  IBEX_SPIN_FOR(phase++ == kCurrentTestPhase, kCurrentTestPhaseTimeoutUsec);
  // Check that the interrupt isn't triggered at the first part of the test.
  CHECK(peripheral == UINT32_MAX,
        "The interrupt is triggered during input glitch.");
  test_phase_sync();

  wait_for_interrupt();
  // Check that the interrupt is triggered at the second part of the test.
  CHECK(peripheral == kTopEarlgreyPlicPeripheralSysrstCtrlAon,
        "The interrupt is not triggered during the test.");
  CHECK(irq_id == kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected,
        "Wrong irq_id");

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
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralSysrstCtrlAon) {
    irq =
        (dif_sysrst_ctrl_irq_t)(irq_id -
                                (dif_rv_plic_irq_id_t)
                                    kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected);
    CHECK_DIF_OK(dif_sysrst_ctrl_irq_acknowledge(&sysrst_ctrl, irq));
  }

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
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

  // Enable sysrst ctrl irq.
  dif_toggle_t irq_state = kDifToggleEnabled;
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlIrqEventDetected, irq_state));

  // Set input pins.
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  for (int i = 0; i < kOutputNunMioPads; ++i) {
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
