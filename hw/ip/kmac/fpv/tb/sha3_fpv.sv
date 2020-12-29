// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module sha3_fpv
  import sha3_pkg::*;
#(
  // Enable Masked Keccak if 1
  parameter  bit EnMasking = 0,
  localparam int Share = (EnMasking) ? 2 : 1
)(
  input clk_i,
  input rst_ni,

  // MSG interface
  input                       msg_valid_i,
  input        [MsgWidth-1:0] msg_data_i [Share],
  input        [MsgStrbW-1:0] msg_strb_i,         // one masking for shares
  output logic                msg_ready_o,

  // Entropy interface
  input                     rand_valid_i,
  input        [StateW-1:0] rand_data_i,
  output logic              rand_consumed_o,

  // N, S: Used in cSHAKE mode only
  input [NSRegisterSize*8-1:0] ns_data_i, // See kmac_pkg for details

  // configurations
  input sha3_mode_e       mode_i,     // see sha3pad for details
  input keccak_strength_e strength_i, // see sha3pad for details

  // controls
  input start_i,   // see sha3pad for details
  input process_i, // see sha3pad for details
  input run_i,
  input done_i,    // see sha3pad for details

  output logic absorbed_o,

  output sha3_st_e sha3_fsm_o,

  // digest output
  // This value is valid only after all absorbing process is completed.
  output logic              state_valid_o,
  output logic [StateW-1:0] state_o [Share],

  output err_t error_o
);

  sha3 #(
    .EnMasking(EnMasking),
    .ReuseShare (0)
  ) u_sha3 (
    .*
  );

  // Assumption for testvector
  `ASSUME(Sha3Only_a, mode_i == Sha3)
  `ASSUME(L256Only_a, strength_i == L256)

endmodule
