// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "ast_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_clkmgr_t clkmgr;
static dif_usbdev_t usbdev;
static dif_pinmux_t pinmux;

static uint32_t device_usb_count;
static uint32_t aon_clk_period_us;

// Copied from sw/device/lib/testing/clkgmr_testutils.c
static uint32_t cast_safely(uint64_t val) {
  CHECK(val <= UINT32_MAX);
  return (uint32_t)val;
}

static inline uint32_t get_count_variability(uint32_t cycles,
                                             uint32_t variability_percentage) {
  return ((cycles * variability_percentage) + 99) / 100 + 1;
}

typedef struct expected_count_info {
  uint32_t count;
  uint32_t variability;
} expected_count_info_t;

static expected_count_info_t usb_count_info;
static uint32_t kVariabilityPercentage = 5;

// This variable can be overwritten from the TB side side to speed up
// simulation. By default, it is set to 1ms, which matches the nominal sof
// packet interval. During simulation however, waiting for a few ms can be very
// costly in real time, so we give the testbench the option to override this
// value and speed things up.
static volatile const uint32_t kSoFPeriodUs = 1000;

static void enable_usb_meas_get_code(dif_clkmgr_t *clkmgr,
                                     dif_clkmgr_recov_err_codes_t *codes) {
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_count(
      clkmgr, kDifClkmgrMeasureClockUsb,
      usb_count_info.count - usb_count_info.variability,
      usb_count_info.count + usb_count_info.variability));

  // Wait for measurements to go through a few cycles.
  busy_spin_micros(5 * aon_clk_period_us);

  CHECK_DIF_OK(dif_clkmgr_recov_err_code_get_codes(clkmgr, codes));
};

bool test_main(void) {
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  aon_clk_period_us =
      cast_safely(udiv64_slow(1000 * 1000, kClockFreqAonHz, NULL));
  LOG_INFO("Each aon clock is %d us", aon_clk_period_us);

  device_usb_count =
      cast_safely(udiv64_slow(kClockFreqUsbHz, kClockFreqAonHz, NULL));

  usb_count_info.count = device_usb_count - 1;
  usb_count_info.variability =
      get_count_variability(device_usb_count, kVariabilityPercentage);

  // First, connect usb.
  LOG_INFO("Enable usb");
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselConstantOne));

  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleEnabled));

  dif_clkmgr_recov_err_codes_t codes = 0;

  CHECK_DIF_OK(
      dif_clkmgr_disable_measure_counts(&clkmgr, kDifClkmgrMeasureClockUsb));
  CHECK_DIF_OK(dif_clkmgr_recov_err_code_clear_codes(&clkmgr, codes));
  busy_spin_micros(5 * aon_clk_period_us);

  // Third, wait for usbdev sof calibration to execute
  LOG_INFO("Wait for sof to calibrate clocks");
  // Wait for a few sofs.
  busy_spin_micros((AST_PARAM_NUM_USB_BEACON_PULSES + 2) * kSoFPeriodUs);

  // Last, measure clocks after usb calibration. They should be very accurate.
  // re-enable measurements.
  enable_usb_meas_get_code(&clkmgr, &codes);

  if (codes) {
    LOG_FATAL("Error code is non-zero 0x%h", codes);
  }

  LOG_INFO("sof complete");
  return true;
}
