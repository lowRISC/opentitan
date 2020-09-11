// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle interface for performing life cycle transitions in OTP.
//

`include "prim_assert.sv"

module otp_ctrl_lci
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Lifecycle partition information
  parameter part_info_t Info
) (
  input                               clk_i,
  input                               rst_ni,
  // Escalation input. This moves the FSM into a terminal state and locks down
  // the partition.
  input  lc_tx_t                      escalate_en_i,

  // TODO: add lifecycle transition interface
  // Output error state of partition, to be consumed by OTP error/alert logic.
  // Note that most errors are not recoverable and move the partition FSM into
  // a terminal error state.
  output otp_err_e                    error_o,
  output logic                        lci_idle_o,
  // OTP interface
  output logic                        otp_req_o,
  output prim_otp_cmd_e               otp_cmd_o,
  output logic [OtpSizeWidth-1:0]     otp_size_o,
  output logic [OtpIfWidth-1:0]       otp_wdata_o,
  output logic [OtpAddrWidth-1:0]     otp_addr_o,
  input                               otp_gnt_i,
  input                               otp_rvalid_i,
  input  [ScrmblBlockWidth-1:0]       otp_rdata_i,
  input  otp_err_e                    otp_err_i
);

endmodule : otp_ctrl_lci
