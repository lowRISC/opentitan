// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rstmgr_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

status_t rstmgr_testutils_is_reset_info(const dif_rstmgr_t *rstmgr,
                                        dif_rstmgr_reset_info_bitfield_t info) {
  dif_rstmgr_reset_info_bitfield_t actual_info;
  actual_info = rstmgr_testutils_reason_get();
  return OK_STATUS(actual_info == info);
}

status_t rstmgr_testutils_reset_info_any(
    const dif_rstmgr_t *rstmgr, dif_rstmgr_reset_info_bitfield_t info) {
  dif_rstmgr_reset_info_bitfield_t actual_info;
  actual_info = rstmgr_testutils_reason_get();
  return OK_STATUS((actual_info & info) != 0);
}

status_t rstmgr_testutils_compare_alert_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t dump_size) {
  size_t size_read;
  dif_rstmgr_alert_info_dump_segment_t
      actual_alert_dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];

  TRY(dif_rstmgr_alert_info_dump_read(
      rstmgr, actual_alert_dump, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &size_read));
  TRY_CHECK(dump_size == size_read,
            "The expected alert info dump size (%d) is not equal to "
            "the observed dump size (%d).",
            dump_size, size_read);
  TRY_CHECK_ARRAYS_EQ(actual_alert_dump, expected_alert_dump, dump_size);
  return OK_STATUS();
}

status_t rstmgr_testutils_compare_cpu_info(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump, size_t dump_size) {
  size_t size_read;
  dif_rstmgr_cpu_info_dump_segment_t
      actual_cpu_dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];

  TRY(dif_rstmgr_cpu_info_dump_read(rstmgr, actual_cpu_dump,
                                    DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
  TRY_CHECK(dump_size == size_read,
            "The expected cpu info dump size (%d) is not equal to "
            "the observed dump size (%d).",
            dump_size, size_read);
  TRY_CHECK_ARRAYS_EQ(actual_cpu_dump, expected_cpu_dump, dump_size);
  return OK_STATUS();
}

status_t rstmgr_testutils_pre_reset(const dif_rstmgr_t *rstmgr) {
  // Clear reset_info.
  rstmgr_testutils_reason_clear();

  // Enable alert and cpu dump capture, even if the test doesn't read it.
  TRY(dif_rstmgr_alert_info_set_enabled(rstmgr, kDifToggleEnabled));
  TRY(dif_rstmgr_cpu_info_set_enabled(rstmgr, kDifToggleEnabled));
  return OK_STATUS();
}

status_t rstmgr_testutils_post_reset(
    const dif_rstmgr_t *rstmgr,
    dif_rstmgr_reset_info_bitfield_t expected_reset_info,
    dif_rstmgr_alert_info_dump_segment_t *expected_alert_dump,
    size_t alert_dump_size,
    dif_rstmgr_cpu_info_dump_segment_t *expected_cpu_dump,
    size_t cpu_dump_size) {
  // Read and compare reset_info.
  dif_rstmgr_reset_info_bitfield_t actual_reset_info;
  actual_reset_info = rstmgr_testutils_reason_get();
  TRY_CHECK(expected_reset_info == actual_reset_info,
            "Unexpected reset_info CSR mismatch, expected 0x%x, got 0x%x",
            expected_reset_info, actual_reset_info);

  if (expected_alert_dump != NULL && alert_dump_size != 0) {
    TRY(rstmgr_testutils_compare_alert_info(rstmgr, expected_alert_dump,
                                            alert_dump_size));
  }
  if (expected_cpu_dump != NULL && cpu_dump_size != 0) {
    TRY(rstmgr_testutils_compare_cpu_info(rstmgr, expected_cpu_dump,
                                          cpu_dump_size));
  }
  return OK_STATUS();
}

dif_rstmgr_reset_info_bitfield_t rstmgr_testutils_reason_get() {
  return retention_sram_get()->reset_reasons;
}

void rstmgr_testutils_reason_clear() {
  retention_sram_get()->reset_reasons = 0;
}
