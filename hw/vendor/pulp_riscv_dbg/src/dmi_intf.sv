// Copyright 2021 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>


// The DV interface additionally carries a clock signal.
interface DMI_BUS_DV #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1
) (
  input logic clk_i
);

  import dm::*;

  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [31:0] data_t;
  /// The request channel (Q).
  addr_t   q_addr;
  dtm_op_e q_op;
  data_t   q_data;
  logic    q_valid;
  logic    q_ready;

  /// The response channel (P).
  data_t   p_data;
  logic    p_resp;
  logic    p_valid;
  logic    p_ready;

  modport in  (
    input  q_addr, q_op, q_data, q_valid, p_ready,
    output q_ready, p_data, p_resp, p_valid
  );
  modport out (
    output q_addr, q_op, q_data, q_valid, p_ready,
    input  q_ready, p_data, p_resp, p_valid
  );
  modport monitor (
    input q_addr, q_op, q_data, q_valid, p_ready,
          q_ready, p_data, p_resp, p_valid
  );

  // pragma translate_off
  `ifndef VERILATOR
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_addr)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_op)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> $stable(q_data)));
  assert property (@(posedge clk_i) (q_valid && !q_ready |=> q_valid));

  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_data)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> $stable(p_resp)));
  assert property (@(posedge clk_i) (p_valid && !p_ready |=> p_valid));
  `endif
  // pragma translate_on

endinterface
