// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic Asynchronous SRAM FIFO (Dual port SRAM)

`include "prim_assert.sv"

module prim_fifo_async_sram_adapter #(
  parameter int unsigned Width = 32,
  parameter int unsigned Depth = 16,

  // SRAM parameters
  parameter int unsigned       SramAw = 16,

  // If SramDw > Width, upper data bits are 0.
  parameter int unsigned       SramDw = 32,
  parameter logic [SramAw-1:0] SramBaseAddr = 'h 0,

  // derived
  localparam int unsigned DepthW = $clog2(Depth+1)
) (
  // Write port
  input                     clk_wr_i,
  input                     rst_wr_ni,
  input                     wvalid_i,
  output logic              wready_o,
  input        [Width-1:0]  wdata_i,
  output logic [DepthW-1:0] wdepth_o,

  // Read port
  input                     clk_rd_i,
  input                     rst_rd_ni,
  output logic              rvalid_o,
  input                     rready_i,
  output logic [Width-1:0]  rdata_o,
  output logic [DepthW-1:0] rdepth_o,

  output logic r_full_o,
  output logic r_notempty_o,

  output logic w_full_o,

  // TODO: watermark(threshold) ?

  // SRAM interface
  // Write SRAM port
  output logic              w_sram_req_o,
  input                     w_sram_gnt_i,
  output logic              w_sram_write_o,
  output logic [SramAw-1:0] w_sram_addr_o,
  output logic [SramDw-1:0] w_sram_wdata_o,
  output logic [SramDw-1:0] w_sram_wmask_o,
  input                     w_sram_rvalid_i, // not used
  input        [SramDw-1:0] w_sram_rdata_i,  // not used
  input        [1:0]        w_sram_rerror_i, // not used

  // Read SRAM port
  output logic              r_sram_req_o,
  input                     r_sram_gnt_i,
  output logic              r_sram_write_o,
  output logic [SramAw-1:0] r_sram_addr_o,
  output logic [SramDw-1:0] r_sram_wdata_o, // not used
  output logic [SramDw-1:0] r_sram_wmask_o, // not used
  input                     r_sram_rvalid_i,
  input        [SramDw-1:0] r_sram_rdata_i,
  input        [1:0]        r_sram_rerror_i
);

  ////////////////
  // Definition //
  ////////////////
  // w_: write clock domain signals
  // r_: read clock domain signals

  // PtrVW: Pointer Value (without msb, flip) width
  localparam int unsigned PtrVW = $clog2(Depth);
  // PtrW: Read/Write pointer with flip bit
  localparam int unsigned PtrW  = PtrVW+1;

  ////////////
  // Signal //
  ////////////

  logic [PtrW-1:0]  w_wptr_q, w_wptr_d, w_wptr_gray_d, w_wptr_gray_q;
  logic [PtrW-1:0]  r_wptr_gray, r_wptr;
  logic [PtrVW-1:0] w_wptr_v, r_wptr_v;
  logic             w_wptr_p, r_wptr_p; // phase

  logic [PtrW-1:0]  r_rptr_q, r_rptr_d, r_rptr_gray_d, r_rptr_gray_q;
  logic [PtrW-1:0]  w_rptr_gray, w_rptr;
  logic [PtrVW-1:0] r_rptr_v, w_rptr_v;
  logic             r_rptr_p, w_rptr_p; // phase

  logic w_wptr_inc, r_rptr_inc;

  logic w_full, r_full, r_empty;

  // SRAM response one clock delayed. So store the value into read clock
  // domain
  logic             stored;
  logic [Width-1:0] rdata_q, rdata_d;

  // SRAM has another read pointer (for address of SRAM req)
  // It is -1 of r_rptr if stored, else same to r_rptr
  logic            r_sram_rptr_inc;
  logic [PtrW-1:0] r_sram_rptr;

  // r_sram_rptr == r_wptr
  // Used to determine r_sram_req
  logic r_sramrptr_empty;

  logic rfifo_ack; // Used to check if FIFO read interface consumes a data
  logic rsram_ack;

  //////////////
  // Datapath //
  //////////////

  // Begin: Write pointer sync to read clock ========================
  assign w_wptr_inc = wvalid_i & wready_o;

  assign w_wptr_d = w_wptr_q + PtrW'(1);

  always_ff @(posedge clk_wr_i or negedge rst_wr_ni) begin
    if (!rst_wr_ni) begin
      w_wptr_q      <= PtrW'(0);
      w_wptr_gray_q <= PtrW'(0);
    end else if (w_wptr_inc) begin
      w_wptr_q      <= w_wptr_d;
      w_wptr_gray_q <= w_wptr_gray_d;
    end
  end

  assign w_wptr_v = w_wptr_q[0+:PtrVW];
  assign w_wptr_p = w_wptr_q[PtrW-1];

  assign w_wptr_gray_d = dec2gray(w_wptr_d);

  prim_flop_2sync #(
    .Width (PtrW)
  ) u_sync_wptr_gray (
    .clk_i  (clk_rd_i),
    .rst_ni (rst_rd_ni),
    .d_i    (w_wptr_gray_q),
    .q_o    (r_wptr_gray)
  );

  assign r_wptr   = gray2dec(r_wptr_gray);
  assign r_wptr_p = r_wptr[PtrW-1];
  assign r_wptr_v = r_wptr[0+:PtrVW];

  assign wdepth_o = (w_wptr_p == w_rptr_p)
                  ? DepthW'(w_wptr_v - w_rptr_v)
                  : DepthW'({1'b1, w_wptr_v} - {1'b 0, w_rptr_v});
  // End:   Write pointer sync to read clock ------------------------

  // Begin: Read pointer sync to write clock ========================
  //assign r_rptr_inc = rvalid_o & rready_i;
  //assign r_rptr_inc = r_sram_req_o && r_sram_gnt_i;
  // Increase the read pointer (crossing the clock domain) only when the
  // reader acked.
  assign r_rptr_inc = rfifo_ack;

  assign r_rptr_d = r_rptr_q + PtrW'(1);

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      r_rptr_q      <= PtrW'(0);
      r_rptr_gray_q <= PtrW'(0);
    end else if (r_rptr_inc) begin
      r_rptr_q      <= r_rptr_d;
      r_rptr_gray_q <= r_rptr_gray_d;
    end
  end

  assign r_rptr_v = r_rptr_q[0+:PtrVW];
  assign r_rptr_p = r_rptr_q[PtrW-1];

  assign r_rptr_gray_d = dec2gray(r_rptr_d);

  prim_flop_2sync #(
    .Width (PtrW)
  ) u_sync_rptr_gray (
    .clk_i  (clk_wr_i),
    .rst_ni (rst_wr_ni),
    .d_i    (r_rptr_gray_q),
    .q_o    (w_rptr_gray)
  );

  assign w_rptr = gray2dec(w_rptr_gray);
  assign w_rptr_p = w_rptr[PtrW-1];
  assign w_rptr_v = w_rptr[0+:PtrVW];

  assign rdepth_o = (r_wptr_p == r_rptr_p)
                  ? DepthW'(r_wptr_v - r_rptr_v)
                  : DepthW'({1'b1, r_wptr_v} - {1'b 0, r_rptr_v});
  // End:   Read pointer sync to write clock ------------------------

  // Begin: SRAM Read pointer
  assign r_sram_rptr_inc = rsram_ack;

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      r_sram_rptr <= PtrW'(0);
    end else if (r_sram_rptr_inc) begin
      r_sram_rptr <= r_sram_rptr + PtrW'(1);
    end
  end

  assign r_sramrptr_empty = (r_wptr == r_sram_rptr);
  // End:   SRAM Read pointer

  // Full/ Empty
  // Lint complains PtrW'(1) << (PtrW-1). So changed as below
  localparam logic [PtrW-1:0] XorMask = {1'b 1, {PtrW-1{1'b0}}};
  assign w_full  = (w_wptr_q == (w_rptr   ^ XorMask));
  assign r_full  = (r_wptr   == (r_rptr_q ^ XorMask));
  assign r_empty = (r_wptr   == r_rptr_q);

  logic  unused_r_empty;
  assign unused_r_empty = r_empty;

  assign r_full_o     = r_full;
  assign w_full_o     = w_full;

  // The notempty status !(wptr == rptr) assert one clock earlier than the
  // actual `rvalid` signals.
  //
  // The reason is due to the SRAM read latency. The module uses SRAM FIFO
  // interface. When the logic in producer domain pushes entries, the pointer
  // is increased. This triggers the FIFO logic in the consumer clock domain
  // fetches data from SRAM.
  //
  // The pointer crosses the clock boundary. It takes usually two cycles (in
  // the consumer side). Then, as the read and write pointer in the read clock
  // domain has a gap by 1, the FIFO not empty status is raised.
  //
  // At this time, the logic just sent the read request to the SRAM. The data
  // is not yet read. The `rvalid` asserts when it receives data from the
  // SRAM.
  //
  // So, if the consumer reads data at the same cycle when notempty status is
  // raised, it reads incorrect data.
  assign r_notempty_o = rvalid_o;

  assign rsram_ack = r_sram_req_o && r_sram_gnt_i;
  assign rfifo_ack = rvalid_o     && rready_i;

  // SRAM Write Request
  assign w_sram_req_o   = wvalid_i && !w_full;
  assign wready_o       = !w_full && w_sram_gnt_i;
  assign w_sram_write_o = 1'b 1; // Always write
  assign w_sram_addr_o  = SramBaseAddr + SramAw'(w_wptr_v);

  assign w_sram_wdata_o = SramDw'(wdata_i);
  assign w_sram_wmask_o = SramDw'({Width{1'b1}});

  logic unused_w_sram;
  assign unused_w_sram = ^{w_sram_rvalid_i, w_sram_rdata_i, w_sram_rerror_i};

  // SRAM Read Request
  // Request Scenario (!r_empty):
  //  - storage empty: Send request if
  //               !r_sram_rvalid_i || (rfifo_ack && r_sram_rvalid_i);
  //  - storage !empty: depends on the rfifo_ack:
  //    - r_rptr_inc: Can request more
  //    - !r_rptr_inc: Can't request
  always_comb begin : r_sram_req
    r_sram_req_o = 1'b 0;
    // Karnough Map (!empty): sram_req
    // {sram_rv, rfifo_ack} | 00 | 01          | 11 | 10
    // ----------------------------------------------------------
    // stored          | 0  |  1 |  impossible |  1 |  0
    //                 | 1  |  0 |  1          |  X |  impossible
    //
    // req_o = r_ptr_inc || (!stored && !r_sram_rvalid_i)

    if (stored) begin
      // storage has data. depends on rfifo_ack
      // rfifo_ack can be replaced to rready_i as `rvalid_o` is 1
      r_sram_req_o = !r_sramrptr_empty && rfifo_ack;
    end else begin
      // storage has no data.
      // Can send request only when the reader accept the request or no
      // previous request sent out.
      r_sram_req_o = !r_sramrptr_empty && !(r_sram_rvalid_i ^ rfifo_ack);
    end
  end : r_sram_req

  assign rvalid_o       = stored || r_sram_rvalid_i;
  assign r_sram_write_o = 1'b 0; // always read
  assign r_sram_wdata_o = '0;
  assign r_sram_wmask_o = '0;

  // Send SRAM request with sram read pointer.
  assign r_sram_addr_o  = SramBaseAddr + SramAw'(r_sram_rptr[0+:PtrVW]);

  assign rdata_d = (r_sram_rvalid_i) ? r_sram_rdata_i[0+:Width] : Width'(0);

  assign rdata_o = (stored) ? rdata_q : rdata_d;

  logic unused_rsram;
  assign unused_rsram = ^{r_sram_rerror_i};

  if (Width < SramDw) begin : g_unused_rdata
    logic unused_rdata;
    assign unused_rdata = ^r_sram_rdata_i[SramDw-1:Width];
  end : g_unused_rdata

  // read clock domain rdata storage
  logic store_en;

  // Karnough Map (r_sram_rvalid_i):
  // rfifo_ack   | 0 | 1 |
  // ---------------------
  // stored    0 | 1 | 0 |
  //           1 | 0 | 1 |
  //
  // stored = s.r.v && XNOR(stored, rptr_inc)
  assign store_en = r_sram_rvalid_i && !(stored ^ rfifo_ack);

  always_ff @(posedge clk_rd_i or negedge rst_rd_ni) begin
    if (!rst_rd_ni) begin
      stored <= 1'b 0;
      rdata_q <= Width'(0);
    end else if (store_en) begin
      stored <= 1'b 1;
      rdata_q <= rdata_d;
    end else if (!r_sram_rvalid_i && rfifo_ack) begin
      // No request sent, host reads the data
      stored <= 1'b 0;
      rdata_q <= Width'(0);
    end
  end

  //////////////
  // Function //
  //////////////

  // dec2gray / gray2dec copied from prim_fifo_async.sv
  function automatic [PtrW-1:0] dec2gray(input logic [PtrW-1:0] decval);
    logic [PtrW-1:0] decval_sub;
    logic [PtrW-1:0] decval_in;
    logic            unused_decval_msb;

    decval_sub = (PtrW)'(Depth) - {1'b0, decval[PtrW-2:0]} - 1'b1;

    decval_in = decval[PtrW-1] ? decval_sub : decval;

    // We do not care about the MSB, hence we mask it out
    unused_decval_msb = decval_in[PtrW-1];
    decval_in[PtrW-1] = 1'b0;

    // Perform the XOR conversion
    dec2gray = decval_in;
    dec2gray ^= (decval_in >> 1);

    // Override the MSB
    dec2gray[PtrW-1] = decval[PtrW-1];
  endfunction

  // Algorithm walks up from 0..N-1 then flips the upper bit and walks down from N-1 to 0.
  function automatic [PtrW-1:0] gray2dec(input logic [PtrW-1:0] grayval);
    logic [PtrW-1:0] dec_tmp, dec_tmp_sub;
    logic            unused_decsub_msb;

    dec_tmp = '0;
    for (int i = PtrW-2; i >= 0; i--) begin
      dec_tmp[i] = dec_tmp[i+1] ^ grayval[i];
    end
    dec_tmp_sub = (PtrW)'(Depth) - dec_tmp - 1'b1;
    if (grayval[PtrW-1]) begin
      gray2dec = dec_tmp_sub;
      // Override MSB
      gray2dec[PtrW-1] = 1'b1;
      unused_decsub_msb = dec_tmp_sub[PtrW-1];
    end else begin
      gray2dec = dec_tmp;
    end
  endfunction

  ///////////////
  // Assertion //
  ///////////////

  `ASSERT_INIT(ParamCheckDepth_A, (Depth == 2**$clog2(Depth)))

  // Use FF if less than 4.
  `ASSERT_INIT(MinDepth_A, Depth >= 4)

  // SramDw greather than or equal to Width
  `ASSERT_INIT(WidthMatch_A, SramDw >= Width)

  // Not stored, Not read valid, but rptr_inc case is impossible
  `ASSERT(RptrIncDataValid_A,
          r_rptr_inc |-> stored || r_sram_rvalid_i,
          clk_rd_i, !rst_rd_ni)
  `ASSERT(SramRvalid_A,
          r_sram_rvalid_i |-> !stored || r_rptr_inc,
          clk_rd_i, !rst_rd_ni)

  // FIFO interface
  `ASSERT(NoWAckInFull_A, w_wptr_inc |-> !w_full,
          clk_wr_i, !rst_wr_ni)

  `ASSERT(WptrIncrease_A,
          w_wptr_inc |=> w_wptr_v == PtrVW'($past(w_wptr_v,2) + 1),
          clk_wr_i, !rst_wr_ni)
  `ASSERT(WptrGrayOneBitAtATime_A,
          w_wptr_inc |=> $countones(w_wptr_gray_q ^ $past(w_wptr_gray_q,2)) == 1,
          clk_wr_i, !rst_wr_ni)

  `ASSERT(NoRAckInEmpty_A, r_rptr_inc |-> !r_empty,
          clk_rd_i, !rst_rd_ni)

  `ASSERT(RptrIncrease_A,
          r_rptr_inc |=> PtrVW'($past(r_rptr_v) + 1) == r_rptr_v,
          clk_rd_i, !rst_rd_ni)
  `ASSERT(RptrGrayOneBitAtATime_A,
          r_rptr_inc |=> $countones(r_rptr_gray_q ^ $past(r_rptr_gray_q)) == 1,
          clk_rd_i, !rst_rd_ni)

  // SRAM interface
  `ASSERT(WSramRvalid_A, !w_sram_rvalid_i, clk_wr_i, !rst_wr_ni)
  `ASSUME_FPV(WSramRdataError_M, w_sram_rdata_i == '0 && w_sram_rerror_i == '0,
              clk_wr_i, !rst_wr_ni)

  `ASSUME(RSramRvalidOneCycle_M,
          r_sram_req_o && r_sram_gnt_i |=> r_sram_rvalid_i,
          clk_rd_i, !rst_rd_ni)
  `ASSUME_FPV(RErrorTied_M, r_sram_rerror_i == '0,
              clk_rd_i, !rst_rd_ni)


  // FPV coverage
  `COVER_FPV(WFull_C, w_full, clk_wr_i, !rst_wr_ni)

endmodule : prim_fifo_async_sram_adapter
