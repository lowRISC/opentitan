// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_controller and used to help collect operational state information for
// coverage.

interface otbn_controller_if (
  input       clk_i,
  input       rst_ni,

  // Signal names matching the ones in otbn_controller.
  input otbn_pkg::otbn_state_e state_q
);

  import otbn_pkg::*;

  function automatic otbn_env_pkg::operational_state_e get_operational_state();
    unique case (state_q)
      OtbnStateRun,
      OtbnStateStall:
        return otbn_env_pkg::OperationalStateBusy;

      OtbnStateLocked:
        return otbn_env_pkg::OperationalStateLocked;

      OtbnStateHalt:
        return otbn_env_pkg::OperationalStateIdle;
      default: ;
    endcase
  endfunction

endinterface
