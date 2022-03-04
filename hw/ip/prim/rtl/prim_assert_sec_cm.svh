// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// // Macros and helper code for security countermeasures.

`ifndef PRIM_ASSERT_SEC_CM_SVH
`define PRIM_ASSERT_SEC_CM_SVH

// Helper macros
`define ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_, ERR_NAME_) \
  `ASSERT(FpvSecCm``NAME_``, $rose(PRIM_HIER_.ERR_NAME_) |-> ##[0:MAX_CYCLES_] (ALERT_.alert_p)) \
  `ifdef INC_ASSERT \
  assign PRIM_HIER_.unused_assert_connected = 1'b1; \
  `endif \
  `ASSUME_FPV(``NAME_``TriggerAfterAlertInit_S, $stable(rst_ni) == 0 |-> \
              PRIM_HIER_.ERR_NAME_ == 0 [*10])

// macros for security countermeasures
`define ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_ = 7) \
  `ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_, err_o)

`define ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_ = 7) \
  `ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_, err_o)

`define ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_ = 7) \
  `ASSERT_ERROR_TRIGGER_ALERT(NAME_, PRIM_HIER_, ALERT_, MAX_CYCLES_, unused_err_o)

`endif // PRIM_ASSERT_SEC_CM_SVH
