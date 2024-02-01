// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/sysrst_ctrl_testutils.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

void sysrst_ctrl_testutils_setup_dio(dif_pinmux_t *pinmux) {
  // Make sure that the DIO pins EC reset and flash WP are configured correctly
  // https://opentitan.org/book/hw/ip/sysrst_ctrl/doc/theory_of_operation.html#ec-and-power-on-reset
  // https://opentitan.org/book/hw/ip/sysrst_ctrl/doc/theory_of_operation.html#flash-write-protect-output
  //
  // The documentation says that they should be configured as open drain.
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      .flags = kDifPinmuxPadAttrOpenDrain,
  };
  dif_result_t res = dif_pinmux_pad_write_attrs(
      pinmux, kTopEarlgreyDirectPadsSysrstCtrlAonEcRstL, kDifPinmuxPadKindDio,
      in_attr, &out_attr);
  // The FPGA does not support open drain but instead has virtual open drain.
  // Try to use that if open drain did not work.
  if (res == kDifError && out_attr.flags != kDifPinmuxPadAttrOpenDrain) {
    LOG_INFO(
        "cannot use open drain for sysrst pins, trying virtual open drain");
    in_attr.flags = kDifPinmuxPadAttrVirtualOpenDrain;
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(
        pinmux, kTopEarlgreyDirectPadsSysrstCtrlAonEcRstL, kDifPinmuxPadKindDio,
        in_attr, &out_attr));
    // Note: fallthrough with the modified `in_attr` so that the same attributes
    // are used for both pads.
  }
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(
      pinmux, kTopEarlgreyDirectPadsSysrstCtrlAonFlashWpL, kDifPinmuxPadKindDio,
      in_attr, &out_attr));
}

void sysrst_ctrl_testutils_release_dio(dif_sysrst_ctrl_t *sysrst_ctrl,
                                       bool release_ec, bool release_flash) {
  // Make sure that the DIO pins EC reset and flash WP are released according to
  // the documentation:
  // https://opentitan.org/book/hw/ip/sysrst_ctrl/doc/theory_of_operation.html#ec-and-power-on-reset
  // https://opentitan.org/book/hw/ip/sysrst_ctrl/doc/theory_of_operation.html#flash-write-protect-output
  // We also need to disable the output override mecanism (i.e. "release the
  // pin").
  if (release_ec) {
    dif_sysrst_ctrl_pin_config_t cfg_ec_reset = {
        .enabled = kDifToggleDisabled,
        .allow_zero = true,
        .allow_one = true,
        .override_value = false,
    };
    CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_configure(
        sysrst_ctrl, kDifSysrstCtrlPinEcResetInOut, cfg_ec_reset));
  }
  // Confusingly, the flash WP is different: the value of flash_wp_l_o defaults
  // to logic 0 when it is not explicitly driven via the override function.
  // Therefore to disable the driver we need to *enable* the override and set
  // to 1.
  if (release_flash) {
    dif_sysrst_ctrl_pin_config_t cfg_flash_wp = {
        .enabled = kDifToggleEnabled,
        .allow_zero = false,
        .allow_one = true,
        .override_value = true,
    };
    CHECK_DIF_OK(dif_sysrst_ctrl_output_pin_override_configure(
        sysrst_ctrl, kDifSysrstCtrlPinFlashWriteProtectInOut, cfg_flash_wp));
  }
}

void sysrst_ctrl_testutils_set_ec_rst_pulse_width(
    dif_sysrst_ctrl_t *sysrst_ctrl, uint32_t pulse_us) {
  // The register field counts in aon_clock ticks.
  uint64_t ticks =
      udiv64_slow((uint64_t)pulse_us * kClockFreqAonHz, 1000 * 1000, NULL);
  // The register field is 16-bit wide.
  OT_ASSERT_ENUM_VALUE(SYSRST_CTRL_EC_RST_CTL_EC_RST_PULSE_OFFSET, 0);
  CHECK(ticks <= SYSRST_CTRL_EC_RST_CTL_EC_RST_PULSE_MASK);
  mmio_region_write32(sysrst_ctrl->base_addr, SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
                      (uint16_t)ticks);
}
