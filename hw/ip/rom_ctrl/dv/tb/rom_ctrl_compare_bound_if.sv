// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be bound into an instance of rom_ctrl_compare called u_compare
// and is then able to interact with that module's signals through hierarchical references.
//
// Inside this interface is a rom_ctrl_compare_if, which is not parameterised and can be passed
// safely to an environment.
//
// This nested structure means that the interface used by the environment has no hierarchical
// references to the inside of the design, so the environment (which only refers to the
// rom_ctrl_compare_if type) can be used even if no instance of the interface is bound.

interface rom_ctrl_compare_bound_if #(
  parameter bit                     Bound = 0,
  parameter int unsigned            StateWidth = 1,
  parameter logic [StateWidth-1:0]  Waiting = '0,
  parameter logic [StateWidth-1:0]  Done = '0,
  parameter int                     AW = 1,
  parameter bit [AW-1:0]            LastAddr = '0
) (
  input wire                  clk_i,
  input wire                  rst_ni,

  // The addr_q signal from rom_ctrl_compare, which has AW bits
  input wire [AW-1:0]         addr_q_i,

  // The 5-bit state_q signal from rom_ctrl_compare
  input wire [StateWidth-1:0] state_q_i,

  // The state_d signal from rom_ctrl_compare
  input wire [StateWidth-1:0] state_d_i
);
  if (Bound) begin : gen_bound
    // We want to be able to force addr_q from u_compare_if, without that interface needing to know
    // the width of the signal.
    bit          force_addr;
    int unsigned desired_addr;

    initial forever begin
      wait(force_addr);

      // If force_addr is asserted then we should start to force the signal through addr_q with the
      // value in desired_addr (throwing away any bits above AW-1)
      force u_compare.addr_q = desired_addr[AW-1:0];

      wait(!force_addr);
      release u_compare.addr_q;
    end

    bit       force_state_d;
    bit [4:0] desired_state_d;

    initial forever begin
      wait(force_state_d);
      // Note that forcing the signal works by forcing its bits directly. This is because the signal
      // is an enum whose type is not in scope.
      force u_compare.state_d[4:0] = desired_state_d;
      wait(!force_state_d);
      release u_compare.state_d[4:0];
    end

    rom_ctrl_compare_if u_compare_if (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),

      .param_AW_i       (AW),
      .param_LastAddr_i (32'(LastAddr)),
      .param_Waiting_i  (Waiting),
      .param_Done_i     (Done),

      .addr_q_i          (32'(addr_q_i)),
      .force_addr_q_o    (force_addr),
      .desired_addr_q_o  (desired_addr),

      .state_q_i         (state_q_i),
      .state_d_i         (state_d_i),
      .force_state_d_o   (force_state_d),
      .desired_state_d_o (desired_state_d)
    );
  end

endinterface
