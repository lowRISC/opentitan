// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/clkmgr_testutils.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/dif/dif_clkmgr.h"

static const char *measure_clock_names[kDifClkmgrMeasureClockUsb + 1] = {
    "io_clk", "io_div2_clk", "io_div4_clk", "main_clk", "usb_clk"};

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern bool clkmgr_testutils_get_trans_clock_status(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock);

extern status_t clkmgr_testutils_check_trans_clock_gating(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    bool exp_clock_enabled, uint32_t timeout_usec);

// The thresholds are encoded as
// - max = count + variability
// - min = count - variability
typedef struct expected_count_info {
  uint32_t count;
  uint32_t variability;
} expected_count_info_t;

// The expected counts when jitter is disabled.
static expected_count_info_t kNoJitterCountInfos[kDifClkmgrMeasureClockUsb + 1];

// The expected counts when jitter is enabled.
static expected_count_info_t kJitterCountInfos[kDifClkmgrMeasureClockUsb + 1];

// The expected variability as a percentage. The AST guarantees 3% for all
// clocks, including the AON, so this sets the effective variability to 5%.
static uint32_t kVariabilityPercentage = 5;

// Compute the variability for a given number of cycles, adding an extra cycle
// for synchronizers.
static inline uint32_t get_count_variability(uint32_t cycles,
                                             uint32_t variability_percentage) {
  return ((cycles * variability_percentage) + 99) / 100 + 1;
}

static uint32_t cast_safely(uint64_t val) {
  CHECK(val <= UINT32_MAX);
  return (uint32_t)val;
}

void initialize_expected_counts() {
  // The expected counts depend on the device, per sw/device/lib/arch/device.h.
  // Notice the ratios are small enough to fit a uint32_t, even if the Hz number
  // is in uint64_t.
  // The expected counts are derived from the ratios of the frequencies of the
  // various clocks to the AON clock. For example, 48 Mhz / 200 kHz = 240.
  const uint32_t kDeviceCpuCount =
      cast_safely(udiv64_slow(kClockFreqCpuHz, kClockFreqAonHz,
                              /*rem_out=*/NULL));
  const uint32_t kDeviceIoCount =
      cast_safely(udiv64_slow(kClockFreqPeripheralHz, kClockFreqAonHz,
                              /*rem_out=*/NULL) *
                  4);
  const uint32_t kDeviceIoDiv2Count =
      cast_safely(udiv64_slow(kClockFreqPeripheralHz, kClockFreqAonHz,
                              /*rem_out=*/NULL) *
                  2);
  const uint32_t kDeviceIoDiv4Count =
      cast_safely(udiv64_slow(kClockFreqPeripheralHz, kClockFreqAonHz,
                              /*rem_out=*/NULL));
  const uint32_t kDeviceUsbCount =
      cast_safely(udiv64_slow(kClockFreqUsbHz, kClockFreqAonHz,
                              /*rem_out=*/NULL));

  LOG_INFO("Variability for Io %d is %d", kDeviceIoCount,
           get_count_variability(kDeviceIoCount, kVariabilityPercentage));
  LOG_INFO("Variability for Cpu %d is %d", kDeviceCpuCount,
           get_count_variability(kDeviceCpuCount, kVariabilityPercentage));

  // Each clock count is guaranteed by the AST +- 3%. This includes the AON
  // clock, so we use an effective variability of +- 5%.
  kNoJitterCountInfos[kDifClkmgrMeasureClockIo] =
      (expected_count_info_t){.count = kDeviceIoCount - 1,
                              .variability = get_count_variability(
                                  kDeviceIoCount, kVariabilityPercentage)};
  kNoJitterCountInfos[kDifClkmgrMeasureClockIoDiv2] =
      (expected_count_info_t){.count = kDeviceIoDiv2Count - 1,
                              .variability = get_count_variability(
                                  kDeviceIoDiv2Count, kVariabilityPercentage)};
  kNoJitterCountInfos[kDifClkmgrMeasureClockIoDiv4] =
      (expected_count_info_t){.count = kDeviceIoDiv4Count - 1,
                              .variability = get_count_variability(
                                  kDeviceIoDiv4Count, kVariabilityPercentage)};
  kNoJitterCountInfos[kDifClkmgrMeasureClockMain] =
      (expected_count_info_t){.count = kDeviceCpuCount - 1,
                              .variability = get_count_variability(
                                  kDeviceCpuCount, kVariabilityPercentage)};
  kNoJitterCountInfos[kDifClkmgrMeasureClockUsb] =
      (expected_count_info_t){.count = kDeviceUsbCount - 1,
                              .variability = get_count_variability(
                                  kDeviceUsbCount, kVariabilityPercentage)};

  // If jitter is enabled the low threshold should be up to 20% lower, so
  // the variability is set to 0.1 * max_count, and count as max - 0.1 * max.
  kJitterCountInfos[kDifClkmgrMeasureClockIo] =
      (expected_count_info_t){.count = kDeviceIoCount - kDeviceIoCount / 10,
                              .variability = kDeviceIoCount / 10};
  kJitterCountInfos[kDifClkmgrMeasureClockIoDiv2] = (expected_count_info_t){
      .count = kDeviceIoDiv2Count - kDeviceIoDiv2Count / 10,
      .variability = kDeviceIoDiv2Count / 10};
  kJitterCountInfos[kDifClkmgrMeasureClockIoDiv4] = (expected_count_info_t){
      .count = kDeviceIoDiv4Count - kDeviceIoDiv4Count / 10,
      .variability = kDeviceIoDiv4Count};
  kJitterCountInfos[kDifClkmgrMeasureClockMain] =
      (expected_count_info_t){.count = kDeviceCpuCount - kDeviceCpuCount / 10,
                              .variability = kDeviceCpuCount / 10};
  kJitterCountInfos[kDifClkmgrMeasureClockUsb] =
      (expected_count_info_t){.count = kDeviceUsbCount - kDeviceUsbCount / 10,
                              .variability = kDeviceUsbCount / 10};
}

const char *clkmgr_testutils_measurement_name(
    dif_clkmgr_measure_clock_t clock) {
  switch (clock) {
    case kDifClkmgrMeasureClockIo:
      return "io";
    case kDifClkmgrMeasureClockIoDiv2:
      return "io_div2";
    case kDifClkmgrMeasureClockIoDiv4:
      return "io_div4";
    case kDifClkmgrMeasureClockMain:
      return "main";
    case kDifClkmgrMeasureClockUsb:
      return "usb";
    default:
      LOG_ERROR("Unexpected clock measurement %d", clock);
  }
  return "unexpected clock";
}

status_t clkmgr_testutils_enable_clock_count(const dif_clkmgr_t *clkmgr,
                                             dif_clkmgr_measure_clock_t clock,
                                             uint32_t lo_threshold,
                                             uint32_t hi_threshold) {
  LOG_INFO("Enabling clock count measurement for %s(%d) lo %d hi %d",
           measure_clock_names[clock], clock, lo_threshold, hi_threshold);
  TRY(dif_clkmgr_enable_measure_counts(clkmgr, clock, lo_threshold,
                                       hi_threshold));
  return OK_STATUS();
}

status_t clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
    const dif_clkmgr_t *clkmgr, bool jitter_enabled, bool external_clk,
    bool low_speed) {
  static bool counts_initialized = false;
  if (!counts_initialized) {
    initialize_expected_counts();
    counts_initialized = true;
  }
  TRY_CHECK(!(external_clk && jitter_enabled));
  for (int clk = 0; clk < ARRAYSIZE(kNoJitterCountInfos); ++clk) {
    const expected_count_info_t *count_info;
    if (jitter_enabled) {
      count_info = &kJitterCountInfos[clk];
    } else if (external_clk) {
      if (low_speed) {
        if (clk == kDifClkmgrMeasureClockIo ||
            clk == kDifClkmgrMeasureClockMain) {
          count_info = &kNoJitterCountInfos[kDifClkmgrMeasureClockIoDiv2];
        } else {
          count_info = &kNoJitterCountInfos[clk];
        }
      } else {
        if (clk == kDifClkmgrMeasureClockMain) {
          count_info = &kNoJitterCountInfos[kDifClkmgrMeasureClockIo];
        } else {
          count_info = &kNoJitterCountInfos[clk];
        }
      }
    } else {
      count_info = &kNoJitterCountInfos[clk];
    }
    TRY(clkmgr_testutils_enable_clock_count(
        clkmgr, (dif_clkmgr_measure_clock_t)clk,
        count_info->count - count_info->variability,
        count_info->count + count_info->variability));
  }
  return OK_STATUS();
}

status_t clkmgr_testutils_check_measurement_enables(
    const dif_clkmgr_t *clkmgr, dif_toggle_t expected_status) {
  bool success = true;
  for (int i = kDifClkmgrMeasureClockIo; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    dif_toggle_t actual_status;
    TRY(dif_clkmgr_measure_counts_get_enable(clkmgr, clock, &actual_status));
    if (actual_status != expected_status) {
      LOG_INFO("Unexpected enable for clock %d: expected %s", i,
               (expected_status == kDifToggleEnabled ? "enabled" : "disabled"));
      success = false;
    }
  }
  return OK_STATUS(success);
}

status_t clkmgr_testutils_disable_clock_counts(const dif_clkmgr_t *clkmgr) {
  LOG_INFO("Disabling all clock count measurements");
  for (int i = 0; i <= kDifClkmgrMeasureClockUsb; ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    TRY(dif_clkmgr_disable_measure_counts(clkmgr, clock));
  }
  return OK_STATUS();
}

status_t clkmgr_testutils_check_measurement_counts(const dif_clkmgr_t *clkmgr) {
  status_t result = OK_STATUS();
  dif_clkmgr_recov_err_codes_t err_codes;
  TRY(dif_clkmgr_recov_err_code_get_codes(clkmgr, &err_codes));
  if (err_codes != 0) {
    LOG_ERROR("Unexpected recoverable error codes 0x%x", err_codes);
    result = INTERNAL();
  } else {
    LOG_INFO("Clock measurements are okay");
  }
  // Clear recoverable errors.
  TRY(dif_clkmgr_recov_err_code_clear_codes(clkmgr, ~0u));
  return result;
}

status_t clkmgr_testutils_enable_external_clock_blocking(
    const dif_clkmgr_t *clkmgr, bool is_low_speed) {
  LOG_INFO("Configure clkmgr to enable external clock");
  TRY(dif_clkmgr_external_clock_set_enabled(clkmgr, is_low_speed));
  TRY(dif_clkmgr_wait_for_ext_clk_switch(clkmgr));
  LOG_INFO("Switching to external clock completes");
  return OK_STATUS();
}
