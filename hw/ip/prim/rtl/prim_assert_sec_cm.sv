// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Assertion macros for sec_cm.

`define ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_ = 5) \
  `ASSERT(NAME_, $rose(PRIM_HIER_.err_o) |-> ##[1:MAX_CYCLES_] $rose(ALERT_.alert_p)); \
  \
  assign PRIM_HIER_.unused_assert_covered = 1'b1;
