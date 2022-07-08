// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_rv_plic_t plic;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kTopEarlgreyPlicTargetIbex0,
};

static sysrst_ctrl_isr_ctx_t sysrst_ctrl_ctx = {
    .sysrst_ctrl = &sysrst_ctrl,
    .plic_sysrst_ctrl_start_irq_id =
        kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl,
    .expected_irq = kDifSysrstCtrlIrqSysrstCtrl,
    .is_only_irq = true,
};

static top_earlgrey_plic_peripheral_t peripheral_serviced;
static dif_sysrst_ctrl_irq_t irq_serviced;

enum {
  kNumPads = 0x7,
  kNunMioPads = 0x6,
  kNumCombinations = 0x4,
  kNumInputs = 0x7,
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

static const uint32_t kExpectedIntrCauses[] = {2, 4, 8, 1, 16, 4096, 8192};

// Threshold for debouce and combo detection written by testbench.
static volatile const uint8_t kThreshold = 0;

void ottf_external_isr(void) {
  isr_testutils_sysrst_ctrl_isr(plic_ctx, sysrst_ctrl_ctx, &peripheral_serviced,
                                &irq_serviced);
}

static void enable_irqs(void) {
  // Enable the sysrst_ctrl interrupt.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &plic, kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl,
      kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &plic, kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl,
      kDifRvPlicMaxPriority));
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, 0x0));
  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

static void setup_input_change_detect_configs(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlPinEcResetInOut, kDifToggleDisabled));
  CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlPinFlashWriteProtectInOut,
      kDifToggleDisabled));

  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      &sysrst_ctrl,
      (dif_sysrst_ctrl_input_change_config_t){
          .debounce_time_threshold = kThreshold,
          .input_changes =
              kDifSysrstCtrlInputKey0H2L | kDifSysrstCtrlInputKey1H2L |
              kDifSysrstCtrlInputKey2H2L | kDifSysrstCtrlInputAcPowerPresetH2L |
              kDifSysrstCtrlInputPowerButtonH2L |
              kDifSysrstCtrlInputEcResetL2H |
              kDifSysrstCtrlInputFlashWriteProtectL2H,
      }));
}

static void setup_key_combinations(void) {
  CHECK_DIF_OK(dif_sysrst_ctrl_input_change_detect_configure(
      &sysrst_ctrl, (dif_sysrst_ctrl_input_change_config_t){
                        .debounce_time_threshold = 0, .input_changes = 0}));

  dif_sysrst_ctrl_key_combo_config_t combo_config = {
      .actions = kDifSysrstCtrlKeyComboActionInterrupt,
      .detection_time_threshold = kThreshold,
      .embedded_controller_reset_duration = 0,
      .keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKey1,
  };
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo0, combo_config));

  combo_config.keys = kDifSysrstCtrlKey0 | kDifSysrstCtrlKey2;
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo1, combo_config));

  combo_config.keys = kDifSysrstCtrlKey1 | kDifSysrstCtrlKey2;
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo2, combo_config));

  combo_config.keys =
      kDifSysrstCtrlKeyPowerButton | kDifSysrstCtrlKeyAcPowerPresent;
  CHECK_DIF_OK(dif_sysrst_ctrl_key_combo_detect_configure(
      &sysrst_ctrl, kDifSysrstCtrlKeyCombo3, combo_config));
}

static void do_test(bool is_input_test) {
  uint32_t loop_size = is_input_test ? kNumInputs : kNumCombinations;
  for (int i = 0; i < loop_size; ++i) {
    test_status_set(kTestStatusInWfi);
    wait_for_interrupt();
    test_status_set(kTestStatusInTest);
    busy_spin_micros(20);

    uint32_t int_causes;
    CHECK_DIF_OK(
        dif_sysrst_ctrl_key_combo_irq_get_causes(&sysrst_ctrl, &int_causes));
    CHECK_DIF_OK(
        dif_sysrst_ctrl_key_combo_irq_clear_causes(&sysrst_ctrl, int_causes));
    CHECK(int_causes == (is_input_test ? 0 : 1 << i));
    CHECK_DIF_OK(
        dif_sysrst_ctrl_input_change_irq_get_causes(&sysrst_ctrl, &int_causes));
    CHECK_DIF_OK(dif_sysrst_ctrl_input_change_irq_clear_causes(&sysrst_ctrl,
                                                               int_causes));
    CHECK(int_causes == (is_input_test ? kExpectedIntrCauses[i] : 0));
  }
}

bool test_main(void) {
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));
  CHECK_DIF_OK(dif_sysrst_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR),
      &sysrst_ctrl));
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(
      &sysrst_ctrl, kDifSysrstCtrlIrqSysrstCtrl, kDifToggleEnabled));
  rv_plic_testutils_irq_range_enable(
      &plic, plic_ctx.hart_id, kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl,
      kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl);

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  for (int i = 0; i < kNunMioPads; ++i) {
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, kPeripheralInputs[i], kInputPads[i]));
  }

  enable_irqs();
  setup_input_change_detect_configs();
  do_test(true);
  setup_key_combinations();
  do_test(false);

  return true;
}
