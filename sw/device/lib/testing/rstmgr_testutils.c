// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rstmgr_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"

bool rstmgr_testutils_is_reset_info(const dif_rstmgr_t *rstmgr,
                                    dif_rstmgr_reset_info_bitfield_t info) {
  dif_rstmgr_reset_info_bitfield_t actual_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(rstmgr, &actual_info));
  return actual_info == info;
}

bool rstmgr_testutils_reset_info_any(const dif_rstmgr_t *rstmgr,
                                     dif_rstmgr_reset_info_bitfield_t info) {
  dif_rstmgr_reset_info_bitfield_t actual_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(rstmgr, &actual_info));
  return (actual_info & info) != 0;
}

void rstmgr_testutils_compare_alert_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t dump_size) {
  size_t size_read;
  dif_rstmgr_alert_info_dump_segment_t
      actual_alert_dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];

  if (expected_alert_dump == 0 || dump_size == 0) {
    return;
  }

  CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
      rstmgr, actual_alert_dump, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &size_read));
  CHECK(dump_size <= size_read);
  CHECK_BUFFER(actual_alert_dump, expected_alert_dump, dump_size);
}

void rstmgr_testutils_compare_cpu_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump, size_t dump_size) {
  size_t size_read;
  dif_rstmgr_cpu_info_dump_segment_t
      actual_cpu_dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];

  if (expected_cpu_dump == 0 || dump_size == 0) {
    return;
  }

  CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
      rstmgr, actual_cpu_dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
  CHECK(dump_size <= size_read);
  CHECK_BUFFER(actual_cpu_dump, expected_cpu_dump, dump_size);
}

void rstmgr_testutils_pre_reset(const dif_rstmgr_t *rstmgr) {
  // Clear reset_info.
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(rstmgr));

  // Enable alert and cpu dump capture, even if the test doesn't read it.
  CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(rstmgr, kDifToggleEnabled));
  CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(rstmgr, kDifToggleEnabled));
}

void rstmgr_testutils_post_reset(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_reset_info_bitfield_t expected_reset_info,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t alert_dump_size,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump,
    size_t cpu_dump_size) {
  // Read and compare reset_info.
  dif_rstmgr_reset_info_bitfield_t actual_reset_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(rstmgr, &actual_reset_info));
  CHECK(expected_reset_info == actual_reset_info,
        "Unexpected reset_info CSR mismatch, expected 0x%x, got 0x%x",
        expected_reset_info, actual_reset_info);

  rstmgr_testutils_compare_alert_info(rstmgr, expected_alert_dump,
                                      alert_dump_size);
  rstmgr_testutils_compare_cpu_info(rstmgr, expected_cpu_dump, cpu_dump_size);
}
