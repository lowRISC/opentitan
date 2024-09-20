// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has assertions that check the read-only value of the alert and cpu_info_attr.
interface rstmgr_attrs_sva_if (
  input logic rst_ni,
  input int   actual_alert_info_attr,
  input int   actual_cpu_info_attr,
  input int   expected_alert_info_attr,
  input int   expected_cpu_info_attr
);

  initial
    @(posedge rst_ni) begin
      `ASSERT_I(AlertInfoAttr_A, actual_alert_info_attr == expected_alert_info_attr)
      `ASSERT_I(CpuInfoAttr_A, actual_cpu_info_attr == expected_cpu_info_attr)
    end
endinterface
