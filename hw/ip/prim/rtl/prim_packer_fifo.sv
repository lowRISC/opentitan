// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Supports packed and unpacked modes
// Uses FIFO timing on the control signals
// No masking or flush functions supported

// Timings - case where InW < OutW
// clk_i      __|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__
// wvalid_i   _____|~~~~|_____|~~~~|_____|~~~~|_____|~~~~|___________________
// wdata_i    Val N     |Val N+1   |Val N+2   |Val N+3   |-------------------
// wready_o   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|__________|~~~~~~~~
// rvalid_o   ___________________________________________|~~~~~~~~~~|________
// rdata_o    -------------------------------------------|Val       |--------
// rready_i   _________________________________________________|~~~~|________
// depth_o    0000000000|1111111111|2222222222|3333333333|4444444444|00000000


// Timings - case where InW > OutW
// clk_i      __|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__
// wvalid_i   _____|~~~~|____________________________________________________
// wdata_i    -----|Val |----------------------------------------------------
// wready_o   ~~~~~~~~~~|___________________________________________|~~~~~~~~
// rvalid_o   __________|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|________
// rdata_o    ----------|Val N     |Val N+1   |Val N+2   |Val N+3   |--------
// rready_i   ________________|~~~~|_____|~~~~|_____|~~~~|_____|~~~~|________
// depth_o    0000000000|4444444444|3333333333|2222222222|1111111111|00000000


// Timings - case where InW = OutW
// clk_i      __|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__~~|__|~~|__
// wvalid_i   _____|~~~~|____________________________________________________
// wdata_i    -----|Val |----------------------------------------------------
// wready_o   ~~~~~~~~~~|__________|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// rvalid_o   __________|~~~~~~~~~~|_________________________________________
// rdata_o    ----------|Val       |-----------------------------------------
// rready_i   ________________|~~~~|_________________________________________
// depth_o    0000000000|1111111111|00000000000000000000000000000000000000000


`include "prim_assert.sv"

module prim_packer_fifo #(
  parameter int InW  = 32,
  parameter int OutW = 8,
  // derived parameters
  localparam int MaxW = (InW > OutW) ? InW : OutW,
  localparam int MinW = (InW < OutW) ? InW : OutW,
//  localparam int DepthW = $clog2(MaxW/MinW) + ~|$clog2(MaxW/MinW)
  localparam int DepthW = $clog2(MaxW/MinW)
) (
  input logic clk_i ,
  input logic rst_ni,

  input logic               clr_i,
  input logic               wvalid_i,
  input logic  [InW-1:0]    wdata_i,
  output logic              wready_o,

  output logic              rvalid_o,
  output logic [OutW-1:0]   rdata_o,
  input logic               rready_i,
  output logic [DepthW:0]   depth_o
);


  // signals
  logic  load_data;
  logic  clear_data;

  // flops
  logic [DepthW:0] depth_q, depth_d;
  logic [MaxW-1:0] data_q, data_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      depth_q <= '0;
      data_q  <= '0;
    end else begin
      depth_q <= depth_d;
      data_q  <= data_d;
    end
  end

  assign depth_o = depth_q;

  if (InW < OutW) begin : gen_pack_mode
    logic [MaxW-1:0] wdata_shifted;

    assign wdata_shifted = wdata_i << (depth_q*InW);
    assign clear_data = (rready_i && rvalid_o) || clr_i;
    assign load_data = wvalid_i && wready_o;

    assign depth_d =  clear_data ? '0 :
           load_data ? depth_q+1 :
           depth_q;

    assign data_d = clear_data ? '0 :
           load_data ? (data_q | wdata_shifted) :
           data_q;

    // set outputs
    assign wready_o = !(depth_q == (MaxW/MinW));
    assign rdata_o =  data_q;
    assign rvalid_o = (depth_q == (MaxW/MinW));

  end else begin : gen_unpack_mode
    logic [MaxW-1:0] rdata_shifted; // ri lint_check_waive NOT_READ
    logic            pull_data;
    logic [DepthW:0] ptr_q, ptr_d;
    logic [DepthW:0] lsb_is_one;
    logic [DepthW:0] max_value;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        ptr_q   <= '0;
      end else begin
        ptr_q   <= ptr_d;
      end
    end

    assign lsb_is_one = {{DepthW{1'b0}},1'b1}; // ri lint_check_waive ZERO_REP
    assign   max_value = (MaxW/MinW);
    assign rdata_shifted = data_q >> ptr_q*OutW;
    assign clear_data = (rready_i && (depth_q == lsb_is_one)) || clr_i;
    assign load_data = wvalid_i && wready_o;
    assign pull_data = rvalid_o && rready_i;

    assign depth_d =  clear_data ? '0 :
           load_data ? max_value :
           pull_data ? depth_q-1 :
           depth_q;

    assign ptr_d =  clear_data ? '0 :
           pull_data ? ptr_q+1 :
           ptr_q;

    assign data_d = clear_data ? '0 :
           load_data ? wdata_i :
           data_q;

    // set outputs
    assign wready_o = (depth_q == '0);
    assign rdata_o =  rdata_shifted[OutW-1:0];
    assign rvalid_o = !(depth_q == '0);

  end


  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////

  // If not acked, valid_o should keep asserting
  `ASSERT(ValidOPairedWidthReadyI_A,
          rvalid_o && !rready_i |=> rvalid_o)

  // If output port doesn't accept the data, the data should be stable
  `ASSERT(DataOStableWhenPending_A,
          ##1 rvalid_o && $past(rvalid_o)
          && !$past(rready_i) |-> $stable(rdata_o))


endmodule
