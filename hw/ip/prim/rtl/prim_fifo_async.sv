// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic asynchronous fifo for use in a variety of devices.

`include "prim_assert.sv"

module prim_fifo_async #(
  parameter  int unsigned Width  = 16,
  parameter  int unsigned Depth  = 3,
  localparam int unsigned DepthW = $clog2(Depth+1) // derived parameter representing [0..Depth]
) (
  // write port
  input                  clk_wr_i,
  input                  rst_wr_ni,
  input                  wvalid_i,
  output                 wready_o,
  input [Width-1:0]      wdata_i,
  output [DepthW-1:0]    wdepth_o,

  // read port
  input                  clk_rd_i,
  input                  rst_rd_ni,
  output                 rvalid_o,
  input                  rready_i,
  output [Width-1:0]     rdata_o,
  output [DepthW-1:0]    rdepth_o
);

  `ASSERT_INIT(paramCheckDepth,  Depth >= 3)

  localparam int unsigned PTRV_W = $clog2(Depth);
  localparam logic [PTRV_W-1:0] DepthMinus1 = PTRV_W'(Depth - 1);
  localparam int unsigned PTR_WIDTH = PTRV_W+1;

  logic [PTR_WIDTH-1:0]    fifo_wptr, fifo_rptr;
  logic [PTR_WIDTH-1:0]    fifo_wptr_sync_combi,   fifo_rptr_sync;
  logic [PTR_WIDTH-1:0]    fifo_wptr_gray_sync,    fifo_rptr_gray_sync;
  logic [PTR_WIDTH-1:0]    fifo_wptr_gray,         fifo_rptr_gray;
  logic                    fifo_incr_wptr, fifo_incr_rptr, empty;

  logic full_wclk, full_rclk;

  assign wready_o = !full_wclk;
  assign rvalid_o = !empty;

  // create the write and read pointers

  assign fifo_incr_wptr = wvalid_i & wready_o;
  assign fifo_incr_rptr = rvalid_o & rready_i;

  ///////////////////
  // write pointer //
  ///////////////////

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni)
    if (!rst_wr_ni) begin
      fifo_wptr <= {(PTR_WIDTH){1'b0}};
    end else if (fifo_incr_wptr) begin
      if (fifo_wptr[PTR_WIDTH-2:0] == DepthMinus1) begin
        fifo_wptr <= {~fifo_wptr[PTR_WIDTH-1],{(PTR_WIDTH-1){1'b0}}};
      end else begin
        fifo_wptr <= fifo_wptr + {{(PTR_WIDTH-1){1'b0}},1'b1};
    end
  end

  // gray-coded version
  always_ff @(posedge clk_wr_i or negedge rst_wr_ni)
    if (!rst_wr_ni) begin
      fifo_wptr_gray <= {(PTR_WIDTH){1'b0}};
    end else if (fifo_incr_wptr) begin
      if (fifo_wptr[PTR_WIDTH-2:0] == DepthMinus1) begin
        fifo_wptr_gray <= dec2gray({~fifo_wptr[PTR_WIDTH-1],{(PTR_WIDTH-1){1'b0}}});
      end else begin
        fifo_wptr_gray <= dec2gray(fifo_wptr + {{(PTR_WIDTH-1){1'b0}},1'b1});
      end
    end

  prim_flop_2sync #(.Width(PTR_WIDTH)) sync_wptr (
    .clk_i    (clk_rd_i),
    .rst_ni   (rst_rd_ni),
    .d_i      (fifo_wptr_gray),
    .q_o      (fifo_wptr_gray_sync));

  assign fifo_wptr_sync_combi = gray2dec(fifo_wptr_gray_sync);

  //////////////////
  // read pointer //
  //////////////////

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni)
    if (!rst_rd_ni) begin
      fifo_rptr <= {(PTR_WIDTH){1'b0}};
    end else if (fifo_incr_rptr) begin
      if (fifo_rptr[PTR_WIDTH-2:0] == DepthMinus1) begin
        fifo_rptr <= {~fifo_rptr[PTR_WIDTH-1],{(PTR_WIDTH-1){1'b0}}};
      end else begin
        fifo_rptr <= fifo_rptr + {{(PTR_WIDTH-1){1'b0}},1'b1};
    end
  end

  // gray-coded version
  always_ff @(posedge clk_rd_i or negedge rst_rd_ni)
    if (!rst_rd_ni) begin
      fifo_rptr_gray <= {(PTR_WIDTH){1'b0}};
    end else if (fifo_incr_rptr) begin
      if (fifo_rptr[PTR_WIDTH-2:0] == DepthMinus1) begin
        fifo_rptr_gray <= dec2gray({~fifo_rptr[PTR_WIDTH-1],{(PTR_WIDTH-1){1'b0}}});
      end else begin
        fifo_rptr_gray <= dec2gray(fifo_rptr + {{(PTR_WIDTH-1){1'b0}},1'b1});
      end
    end

  prim_flop_2sync #(.Width(PTR_WIDTH)) sync_rptr (
    .clk_i    (clk_wr_i),
    .rst_ni   (rst_wr_ni),
    .d_i      (fifo_rptr_gray),
    .q_o      (fifo_rptr_gray_sync));

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni)
    if (!rst_wr_ni) begin
      fifo_rptr_sync <= {PTR_WIDTH{1'b0}};
    end else begin
      fifo_rptr_sync <= gray2dec(fifo_rptr_gray_sync);
    end

  //////////////////
  // empty / full //
  //////////////////

  assign  full_wclk = (fifo_wptr == (fifo_rptr_sync ^ {1'b1,{(PTR_WIDTH-1){1'b0}}}));
  assign  full_rclk = (fifo_wptr_sync_combi == (fifo_rptr ^ {1'b1,{(PTR_WIDTH-1){1'b0}}}));

  // Current depth in the write clock side
  logic  wptr_msb;
  logic  rptr_sync_msb;
  logic  [PTRV_W-1:0] wptr_value;
  logic  [PTRV_W-1:0] rptr_sync_value;
  assign wptr_msb = fifo_wptr[PTR_WIDTH-1];
  assign rptr_sync_msb = fifo_rptr_sync[PTR_WIDTH-1];
  assign wptr_value = fifo_wptr[0+:PTRV_W];
  assign rptr_sync_value = fifo_rptr_sync[0+:PTRV_W];
  assign wdepth_o = (full_wclk) ? DepthW'(Depth) :
                    (wptr_msb == rptr_sync_msb) ? DepthW'(wptr_value) - DepthW'(rptr_sync_value) :
                    (DepthW'(Depth) - DepthW'(rptr_sync_value) + DepthW'(wptr_value)) ;

  // Same again in the read clock side
  assign empty = (fifo_wptr_sync_combi ==  fifo_rptr);
  logic  rptr_msb;
  logic  wptr_sync_msb;
  logic  [PTRV_W-1:0] rptr_value;
  logic  [PTRV_W-1:0] wptr_sync_value;
  assign wptr_sync_msb = fifo_wptr_sync_combi[PTR_WIDTH-1];
  assign rptr_msb = fifo_rptr[PTR_WIDTH-1];
  assign wptr_sync_value = fifo_wptr_sync_combi[0+:PTRV_W];
  assign rptr_value = fifo_rptr[0+:PTRV_W];
  assign rdepth_o = (full_rclk) ? DepthW'(Depth) :
                    (wptr_sync_msb == rptr_msb) ? DepthW'(wptr_sync_value) - DepthW'(rptr_value) :
                    (DepthW'(Depth) - DepthW'(rptr_value) + DepthW'(wptr_sync_value)) ;

  /////////////
  // storage //
  /////////////

  logic [Width-1:0] storage [Depth];

  always_ff @(posedge clk_wr_i)
    if (fifo_incr_wptr) begin
      storage[fifo_wptr[PTR_WIDTH-2:0]] <= wdata_i;
    end

  assign rdata_o = storage[fifo_rptr[PTR_WIDTH-2:0]];

  // gray code conversion functions.  algorithm walks up from 0..N-1
  // then flips the upper bit and walks down from N-1 to 0.

  function automatic [PTR_WIDTH-1:0] dec2gray(input logic [PTR_WIDTH-1:0] decval);
    logic [PTR_WIDTH-1:0] decval_sub;
    logic [PTR_WIDTH-2:0] decval_in;
    logic                 unused_decval_msb;

    decval_sub = (PTR_WIDTH)'(Depth) - {1'b0, decval[PTR_WIDTH-2:0]} - 1'b1;

    {unused_decval_msb, decval_in} = decval[PTR_WIDTH-1] ? decval_sub : decval;
    // Was done in two assigns for low bits and top bit
    // but that generates a (bogus) verilator warning, so do in one assign
    dec2gray = {decval[PTR_WIDTH-1],
                {1'b0,decval_in[PTR_WIDTH-2:1]} ^ decval_in[PTR_WIDTH-2:0]};
  endfunction

  function automatic [PTR_WIDTH-1:0] gray2dec(input logic [PTR_WIDTH-1:0] grayval);
    logic [PTR_WIDTH-2:0] dec_tmp, dec_tmp_sub;
    logic                 unused_decsub_msb;

    dec_tmp[PTR_WIDTH-2] = grayval[PTR_WIDTH-2];
    for (int i = PTR_WIDTH-3; i >= 0; i--)
      dec_tmp[i] = dec_tmp[i+1]^grayval[i];
    {unused_decsub_msb, dec_tmp_sub} = (PTR_WIDTH-1)'(Depth) - {1'b0, dec_tmp} - 1'b1;
    if (grayval[PTR_WIDTH-1])
      gray2dec = {1'b1,dec_tmp_sub};
    else
      gray2dec = {1'b0,dec_tmp};
  endfunction

  // TODO: assertions on full, empty, gray transitions

endmodule
