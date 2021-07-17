// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic asynchronous fifo for use in a variety of devices.

`include "prim_assert.sv"

module prim_fifo_async #(
  parameter  int unsigned Width  = 16,
  parameter  int unsigned Depth  = 4,
  parameter  bit OutputZeroIfEmpty = 1'b0, // if == 1 always output 0 when FIFO is empty
  localparam int unsigned DepthW = $clog2(Depth+1) // derived parameter representing [0..Depth]
) (
  // write port
  input  logic              clk_wr_i,
  input  logic              rst_wr_ni,
  input  logic              wvalid_i,
  output logic              wready_o,
  input  logic [Width-1:0]  wdata_i,
  output logic [DepthW-1:0] wdepth_o,

  // read port
  input  logic              clk_rd_i,
  input  logic              rst_rd_ni,
  output logic              rvalid_o,
  input  logic              rready_i,
  output logic [Width-1:0]  rdata_o,
  output logic [DepthW-1:0] rdepth_o
);

  // Depth must be a power of 2 for the gray code pointers to work
  `ASSERT_INIT(ParamCheckDepth_A, (Depth == 2**$clog2(Depth)))

  localparam int unsigned PTRV_W    = (Depth == 1) ? 1 : $clog2(Depth);
  localparam int unsigned PTR_WIDTH = (Depth == 1) ? 1 : PTRV_W+1;

  logic [PTR_WIDTH-1:0] fifo_wptr_q, fifo_wptr_d;
  logic [PTR_WIDTH-1:0] fifo_rptr_q, fifo_rptr_d;
  logic [PTR_WIDTH-1:0] fifo_wptr_sync_combi, fifo_rptr_sync_combi;
  logic [PTR_WIDTH-1:0] fifo_wptr_gray_sync, fifo_rptr_gray_sync, fifo_rptr_sync_q;
  logic [PTR_WIDTH-1:0] fifo_wptr_gray_q, fifo_wptr_gray_d;
  logic [PTR_WIDTH-1:0] fifo_rptr_gray_q, fifo_rptr_gray_d;
  logic                 fifo_incr_wptr, fifo_incr_rptr;
  logic                 full_wclk, full_rclk, empty_rclk;
  logic [Width-1:0]     storage [Depth];

  ///////////////////
  // Write Pointer //
  ///////////////////

  assign fifo_incr_wptr = wvalid_i & wready_o;

  // decimal version
  assign fifo_wptr_d = fifo_wptr_q + PTR_WIDTH'(1'b1);

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      fifo_wptr_q <= '0;
    end else if (fifo_incr_wptr) begin
      fifo_wptr_q <= fifo_wptr_d;
    end
  end

  // gray-coded version
  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      fifo_wptr_gray_q <= '0;
    end else if (fifo_incr_wptr) begin
      fifo_wptr_gray_q <= fifo_wptr_gray_d;
    end
  end

  // sync gray-coded pointer to read clk
  prim_flop_2sync #(.Width(PTR_WIDTH)) sync_wptr (
    .clk_i    (clk_rd_i),
    .rst_ni   (rst_rd_ni),
    .d_i      (fifo_wptr_gray_q),
    .q_o      (fifo_wptr_gray_sync));

  //////////////////
  // Read Pointer //
  //////////////////

  assign fifo_incr_rptr = rvalid_o & rready_i;

  // decimal version
  assign fifo_rptr_d = fifo_rptr_q + PTR_WIDTH'(1'b1);

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      fifo_rptr_q <= '0;
    end else if (fifo_incr_rptr) begin
      fifo_rptr_q <= fifo_rptr_d;
    end
  end

  // gray-coded version
  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      fifo_rptr_gray_q <= '0;
    end else if (fifo_incr_rptr) begin
      fifo_rptr_gray_q <= fifo_rptr_gray_d;
    end
  end

  // sync gray-coded pointer to write clk
  prim_flop_2sync #(.Width(PTR_WIDTH)) sync_rptr (
    .clk_i    (clk_wr_i),
    .rst_ni   (rst_wr_ni),
    .d_i      (fifo_rptr_gray_q),
    .q_o      (fifo_rptr_gray_sync));

  // Registered version of synced read pointer
  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      fifo_rptr_sync_q <= '0;
    end else begin
      fifo_rptr_sync_q <= fifo_rptr_sync_combi;
    end
  end

  //////////////////
  // Empty / Full //
  //////////////////

  logic [PTR_WIDTH-1:0] xor_mask;
  assign xor_mask   =  PTR_WIDTH'(1'b1) << (PTR_WIDTH-1);
  assign full_wclk  = (fifo_wptr_q == (fifo_rptr_sync_q ^ xor_mask));
  assign full_rclk  = (fifo_wptr_sync_combi == (fifo_rptr_q ^ xor_mask));
  assign empty_rclk = (fifo_wptr_sync_combi ==  fifo_rptr_q);

  if (Depth > 1) begin : g_depth_calc

    // Current depth in the write clock side
    logic               wptr_msb;
    logic               rptr_sync_msb;
    logic  [PTRV_W-1:0] wptr_value;
    logic  [PTRV_W-1:0] rptr_sync_value;

    assign wptr_msb        = fifo_wptr_q[PTR_WIDTH-1];
    assign rptr_sync_msb   = fifo_rptr_sync_q[PTR_WIDTH-1];
    assign wptr_value      = fifo_wptr_q[0+:PTRV_W];
    assign rptr_sync_value = fifo_rptr_sync_q[0+:PTRV_W];
    assign wdepth_o = (full_wclk) ? DepthW'(Depth) :
                      (wptr_msb == rptr_sync_msb) ? DepthW'(wptr_value) - DepthW'(rptr_sync_value) :
                      (DepthW'(Depth) - DepthW'(rptr_sync_value) + DepthW'(wptr_value)) ;

    // Current depth in the read clock side
    logic               rptr_msb;
    logic               wptr_sync_msb;
    logic  [PTRV_W-1:0] rptr_value;
    logic  [PTRV_W-1:0] wptr_sync_value;

    assign wptr_sync_msb   = fifo_wptr_sync_combi[PTR_WIDTH-1];
    assign rptr_msb        = fifo_rptr_q[PTR_WIDTH-1];
    assign wptr_sync_value = fifo_wptr_sync_combi[0+:PTRV_W];
    assign rptr_value      = fifo_rptr_q[0+:PTRV_W];
    assign rdepth_o = (full_rclk) ? DepthW'(Depth) :
                      (wptr_sync_msb == rptr_msb) ? DepthW'(wptr_sync_value) - DepthW'(rptr_value) :
                      (DepthW'(Depth) - DepthW'(rptr_value) + DepthW'(wptr_sync_value)) ;

  end else begin : g_no_depth_calc

    assign rdepth_o = full_rclk;
    assign wdepth_o = full_wclk;

  end

  assign wready_o = ~full_wclk;
  assign rvalid_o = ~empty_rclk;

  /////////////
  // Storage //
  /////////////

  logic [Width-1:0] rdata_int;
  if (Depth > 1) begin : g_storage_mux

    always_ff @(posedge clk_wr_i) begin
      if (fifo_incr_wptr) begin
        storage[fifo_wptr_q[PTRV_W-1:0]] <= wdata_i;
      end
    end

    assign rdata_int = storage[fifo_rptr_q[PTRV_W-1:0]];

  end else begin : g_storage_simple

    always_ff @(posedge clk_wr_i) begin
      if (fifo_incr_wptr) begin
        storage[0] <= wdata_i;
      end
    end

    assign rdata_int = storage[0];

  end

  if (OutputZeroIfEmpty == 1'b1) begin : gen_output_zero
    assign rdata_o = empty_rclk ? '0 : rdata_int;
  end else begin : gen_no_output_zero
    assign rdata_o = rdata_int;
  end

  //////////////////////////////////////
  // Decimal <-> Gray-code Conversion //
  //////////////////////////////////////

  // This code is all in a generate context to avoid lint errors when Depth <= 2
  if (Depth > 2) begin : g_full_gray_conversion

    function automatic [PTR_WIDTH-1:0] dec2gray(input logic [PTR_WIDTH-1:0] decval);
      logic [PTR_WIDTH-1:0] decval_sub;
      logic [PTR_WIDTH-1:0] decval_in;
      logic                 unused_decval_msb;

      decval_sub = (PTR_WIDTH)'(Depth) - {1'b0, decval[PTR_WIDTH-2:0]} - 1'b1;

      decval_in = decval[PTR_WIDTH-1] ? decval_sub : decval;

      // We do not care about the MSB, hence we mask it out
      unused_decval_msb = decval_in[PTR_WIDTH-1];
      decval_in[PTR_WIDTH-1] = 1'b0;

      // Perform the XOR conversion
      dec2gray = decval_in;
      dec2gray ^= (decval_in >> 1);

      // Override the MSB
      dec2gray[PTR_WIDTH-1] = decval[PTR_WIDTH-1];
    endfunction

    // Algorithm walks up from 0..N-1 then flips the upper bit and walks down from N-1 to 0.
    function automatic [PTR_WIDTH-1:0] gray2dec(input logic [PTR_WIDTH-1:0] grayval);
      logic [PTR_WIDTH-1:0] dec_tmp, dec_tmp_sub;
      logic                 unused_decsub_msb;

      dec_tmp = '0;
      for (int i = PTR_WIDTH-2; i >= 0; i--) begin
        dec_tmp[i] = dec_tmp[i+1] ^ grayval[i];
      end
      dec_tmp_sub = (PTR_WIDTH)'(Depth) - dec_tmp - 1'b1;
      if (grayval[PTR_WIDTH-1]) begin
        gray2dec = dec_tmp_sub;
        // Override MSB
        gray2dec[PTR_WIDTH-1] = 1'b1;
        unused_decsub_msb = dec_tmp_sub[PTR_WIDTH-1];
      end else begin
        gray2dec = dec_tmp;
      end
    endfunction

    // decimal version of read pointer in write domain
    assign fifo_rptr_sync_combi = gray2dec(fifo_rptr_gray_sync);
    // decimal version of write pointer in read domain
    assign fifo_wptr_sync_combi = gray2dec(fifo_wptr_gray_sync);

    assign fifo_rptr_gray_d = dec2gray(fifo_rptr_d);
    assign fifo_wptr_gray_d = dec2gray(fifo_wptr_d);

  end else if (Depth == 2) begin : g_simple_gray_conversion

    assign fifo_rptr_sync_combi = {fifo_rptr_gray_sync[PTR_WIDTH-1], ^fifo_rptr_gray_sync};
    assign fifo_wptr_sync_combi = {fifo_wptr_gray_sync[PTR_WIDTH-1], ^fifo_wptr_gray_sync};

    assign fifo_rptr_gray_d = {fifo_rptr_d[PTR_WIDTH-1], ^fifo_rptr_d};
    assign fifo_wptr_gray_d = {fifo_wptr_d[PTR_WIDTH-1], ^fifo_wptr_d};

  end else begin : g_no_gray_conversion

    assign fifo_rptr_sync_combi = fifo_rptr_gray_sync;
    assign fifo_wptr_sync_combi = fifo_wptr_gray_sync;

    assign fifo_rptr_gray_d = fifo_rptr_d;
    assign fifo_wptr_gray_d = fifo_wptr_d;

  end

  // TODO: assertions on full, empty
  `ASSERT(GrayWptr_A, $countones(fifo_wptr_gray_q ^ $past(fifo_wptr_gray_q)) <= 1,
          clk_wr_i, !rst_wr_ni)
  `ASSERT(GrayRptr_A, $countones(fifo_rptr_gray_q ^ $past(fifo_rptr_gray_q)) <= 1,
          clk_rd_i, !rst_rd_ni)

endmodule
