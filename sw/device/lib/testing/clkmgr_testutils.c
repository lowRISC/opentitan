// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/clkmgr_testutils.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/dif/dif_clkmgr.h"

#define MODULE_ID MAKE_MODULE_ID('c', 'm', 't')

static_assert(kDtClkmgrCount == 1,
              "this code assumes that there is a single clkmgr");

enum {
  // We do not know the exact number of measurable clocks but
  // there cannot be more than the total number of clocks.
  kMaxMeasureClockCount = kDtClockCount,
};

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

// Map from the DT clock to the clock measurement index.
// For DT clocks without measurements, this will be set to
// an invalid value.
static size_t dt_clk_to_meas_clk[kDtClockCount];

// The expected counts when jitter is disabled.
static expected_count_info_t kNoJitterCountInfos[kMaxMeasureClockCount];

// The expected counts when jitter is enabled.
static expected_count_info_t kJitterCountInfos[kMaxMeasureClockCount];

// Notice the expected variability is set to somewhat less than the added
// variability of the AON and the measured clock.

// The expected variability as a percentage. The AST guarantees 3% for all
// clocks, including the AON, so the effective variability is set to 5%.
static uint32_t kVariabilityPercentage = 5;

// The expected variability when jitter is enabled as a percentage. The AST
// guarantees 10% for jittery clocks and 3% for the AON clock, so the
// effective variability is set to 12%.
static uint32_t kJitterVariabilityPercentage = 12;

// Compute the variability for a given number of cycles, adding an extra cycle
// for synchronizers.
static inline uint32_t get_count_variability(uint32_t cycles,
                                             uint32_t variability_percentage) {
  return ((cycles * variability_percentage) + 99) / 100 + 1;
}

static const char *measure_clock_name(const dif_clkmgr_t *clkmgr,
                                      dif_clkmgr_measure_clock_t clock) {
  dt_clkmgr_t dt;
  dif_result_t res = dif_clkmgr_get_dt(clkmgr, &dt);
  if (res != kDifOk) {
    return "<no dt info>";
  }
  if (clock >= dt_clkmgr_measurable_clock_count(dt)) {
    return "<invalid clock>";
  }
  dt_clkmgr_measurable_clk_t info = dt_clkmgr_measurable_clock(dt, clock);
  // This is not ideal because it relies on top specific names but it's better
  // than just indices.
  switch (info.clock) {
#ifdef OPENTITAN_CLKMGR_HAS_MEAS_CTRL_MAIN
    case kDtClockMain:
      return "main_clk";
#endif
#ifdef OPENTITAN_CLKMGR_HAS_MEAS_CTRL_IO
    case kDtClockIo:
      return "io_clk";
#endif
#ifdef OPENTITAN_CLKMGR_HAS_MEAS_CTRL_IO_DIV2
    case kDtClockIoDiv2:
      return "io_div2_clk";
#endif
#ifdef OPENTITAN_CLKMGR_HAS_MEAS_CTRL_IO_DIV4
    case kDtClockIoDiv4:
      return "io_div4_clk";
#endif
#ifdef OPENTITAN_CLKMGR_HAS_MEAS_CTRL_USB
    case kDtClockUsb:
      return "usb_clk";
#endif
    case kDtClockAon:
    default:
      return "<unknown>";
  }
}

static uint32_t cast_safely(uint64_t val) {
  CHECK(val <= UINT32_MAX);
  return (uint32_t)val;
}

dif_result_t initialize_expected_counts(const dif_clkmgr_t *clkmgr) {
  dt_clkmgr_t clkmgr_dt;
  DIF_RETURN_IF_ERROR(dif_clkmgr_get_dt(clkmgr, &clkmgr_dt));
  // We assume that measurements are made against the clk_aon_i port.
  dt_clock_t aon_clk_dt = dt_clkmgr_clock(clkmgr_dt, kDtClkmgrClockAon);
  dt_clock_t main_clk_dt = dt_clkmgr_clock(clkmgr_dt, kDtClkmgrClockMain);
  uint64_t aon_clk_freq_hz = dt_clock_frequency(aon_clk_dt);

  // Fill the clock map with invalid values.
  for (dt_clock_t dt_clk = 0; dt_clk < kDtClockCount; dt_clk++) {
    dt_clk_to_meas_clk[dt_clk] = dt_clkmgr_measurable_clock_count(clkmgr_dt);
  }

  // Go through all measurable clocks.
  for (size_t clk_idx = 0;
       clk_idx < dt_clkmgr_measurable_clock_count(clkmgr_dt); clk_idx++) {
    dt_clock_t clk_dt = dt_clkmgr_measurable_clock(clkmgr_dt, clk_idx).clock;
    dt_clk_to_meas_clk[clk_dt] = clk_idx;

    uint64_t clk_freq_hz = dt_clock_frequency(clk_dt);
    // The expected counts are derived from the ratios of the frequencies of the
    // various clocks to the AON clock. For example, 48 Mhz / 200 kHz = 240.
    // Notice the ratios are small enough to fit a uint32_t, even if the Hz
    // number is in uint64_t.
    uint32_t clk_count = cast_safely(
        udiv64_slow(clk_freq_hz, aon_clk_freq_hz, /*rem_out=*/NULL));
    uint32_t variability =
        get_count_variability(clk_count, kVariabilityPercentage);
    LOG_INFO("Variability for %s(%d) %d is %d",
             measure_clock_name(clkmgr, clk_idx), clk_idx, clk_count,
             variability);

    // Each clock count is guaranteed by the AST +- 3%. This includes the AON
    // clock, so we use an effective variability of +- 5%.
    kNoJitterCountInfos[clk_idx] = (expected_count_info_t){
        .count = clk_count - 1, .variability = variability};

    // When jitter is enabled only the main clk is affected: the low threshold
    // should be up to 20% lower, so the expected count is set to 0.9 max, and
    // the variability is set per kJitterVariabilityPercentage.
    if (clk_dt != main_clk_dt) {
      kJitterCountInfos[clk_idx] = kNoJitterCountInfos[clk_idx];
    } else {
      kJitterCountInfos[clk_idx] = (expected_count_info_t){
          .count = clk_count - clk_count / 10,
          .variability = get_count_variability(clk_count - clk_count / 10,
                                               kJitterVariabilityPercentage)};
    }
  }

  return kDifOk;
}

status_t clkmgr_testutils_enable_clock_count(const dif_clkmgr_t *clkmgr,
                                             dif_clkmgr_measure_clock_t clock,
                                             uint32_t lo_threshold,
                                             uint32_t hi_threshold) {
  LOG_INFO("Enabling clock count measurement for %s(%d) lo %d hi %d",
           measure_clock_name(clkmgr, clock), clock, lo_threshold,
           hi_threshold);
  TRY(dif_clkmgr_enable_measure_counts(clkmgr, clock, lo_threshold,
                                       hi_threshold));
  return OK_STATUS();
}

status_t clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
    const dif_clkmgr_t *clkmgr, bool jitter_enabled, bool external_clk,
    bool low_speed) {
  static bool counts_initialized = false;
  if (!counts_initialized) {
    TRY(initialize_expected_counts(clkmgr));
    counts_initialized = true;
  }
  TRY_CHECK(!(external_clk && jitter_enabled));

  dt_clkmgr_t clkmgr_dt;
  TRY(dif_clkmgr_get_dt(clkmgr, &clkmgr_dt));

  for (size_t clk = 0; clk < dt_clkmgr_measurable_clock_count(clkmgr_dt);
       ++clk) {
    const expected_count_info_t *count_info;
    if (jitter_enabled) {
      count_info = &kJitterCountInfos[clk];
    } else if (external_clk) {
#if defined(OPENTITAN_IS_EARLGREY)
      dt_clock_t dt_actual_clk =
          dt_clkmgr_measurable_clock(clkmgr_dt, clk).clock;
      // When software switches to an external clock, all clock sources switch
      // to an external source. In particular, the main clock becomes the same
      // as the IO clock.
      if (dt_actual_clk == kDtClockMain) {
        dt_actual_clk = kDtClockIo;
      }
      // If software requests a low speed external clock, internal dividers are
      // stepped down so that divide-by-2 and divide-by-4 remain at their
      // nominal frequencies. On the other hand, the divide-by-1 (i.e. the IO
      // clock) becomes equal to divide-by-2.
      if (low_speed && dt_actual_clk == kDtClockIo) {
        dt_actual_clk = kDtClockIoDiv2;
      }
      CHECK(dt_clk_to_meas_clk[dt_actual_clk] <
                dt_clkmgr_measurable_clock_count(clkmgr_dt),
            "this clock is not measurable!");
      count_info = &kNoJitterCountInfos[dt_clk_to_meas_clk[dt_actual_clk]];
#elif defined(OPENTITAN_IS_DARJEELING)
      TRY_CHECK(false, "Darjeeling has no external clock");
      OT_UNREACHABLE();
#else
#error Unsupported top
#endif
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
  dt_clkmgr_t clkmgr_dt;
  TRY(dif_clkmgr_get_dt(clkmgr, &clkmgr_dt));
  for (size_t i = 0; i < dt_clkmgr_measurable_clock_count(clkmgr_dt); ++i) {
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
  dt_clkmgr_t clkmgr_dt;
  TRY(dif_clkmgr_get_dt(clkmgr, &clkmgr_dt));
  for (size_t i = 0; i < dt_clkmgr_measurable_clock_count(clkmgr_dt); ++i) {
    dif_clkmgr_measure_clock_t clock = (dif_clkmgr_measure_clock_t)i;
    TRY(dif_clkmgr_disable_measure_counts(clkmgr, clock));
  }
  LOG_INFO("Disabling all clock count done");
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
#if defined(OPENTITAN_IS_EARLGREY)
  LOG_INFO("Configure clkmgr to enable external clock");
  TRY(dif_clkmgr_external_clock_set_enabled(clkmgr, is_low_speed));
  TRY(dif_clkmgr_wait_for_ext_clk_switch(clkmgr));
  LOG_INFO("Switching to external clock completes");
#endif
  return OK_STATUS();
}
