// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for prim_fifo_sync.
// Intended to be used with a formal tool.

module prim_fifo_sync_assert_fpv #(
  // can be desabled for deeper FIFOs
  parameter bit EnableDataCheck = 1'b1,
  parameter int unsigned Width = 16,
  parameter bit Pass = 1'b1,
  parameter int unsigned Depth = 4,
  localparam int unsigned DepthWNorm = $clog2(Depth+1),
  localparam int unsigned DepthW = (DepthWNorm == 0) ? 1 : DepthWNorm
) (
  input  clk_i,
  input  rst_ni,
  input  clr_i,
  input  wvalid,
  input  wready,
  input [Width-1:0] wdata,
  input  rvalid,
  input  rready,
  input [Width-1:0] rdata,
  input [DepthW-1:0] depth
);

  /////////////////
  // Assumptions //
  /////////////////

  // no need to consider all possible input words
  // 2-3 different values suffice
  `ASSUME(WdataValues_M, wdata inside {Width'(1'b0), Width'(1'b1), {Width{1'b1}}}, clk_i, !rst_ni)

  ////////////////////////////////
  // Data and Depth Value Check //
  ////////////////////////////////

   if (EnableDataCheck && Depth > 0) begin : gen_data_check

    logic [DepthW+2:0] ref_depth;
    logic [Width-1:0]  ref_rdata;

    // no pointers needed in this case
    if (Depth == 1) begin : gen_no_ptrs

      logic [Width-1:0]  fifo;
      logic [DepthW+2:0] wptr, rptr;

      // this only models the data flow, since the control logic is tested below
      always_ff @(posedge clk_i or negedge rst_ni) begin : p_fifo_model
        if (!rst_ni) begin
          ref_depth <= 0;
        end else begin
          if (clr_i) begin
            ref_depth <= 0;
          end else begin
            if (wvalid && wready && rvalid && rready) begin
              fifo <= wdata;
            end else if (wvalid && wready) begin
              fifo <= wdata;
              ref_depth <= ref_depth + 1;
            end else if (rvalid && rready) begin
              ref_depth <= ref_depth - 1;
            end
          end
        end
      end

      if (Pass) begin : gen_pass
        assign ref_rdata = (ref_depth == 0) ? wdata : fifo;
      end else begin : no_pass
        assign ref_rdata = fifo;
      end

    // general case
    end else begin : gen_ptrs

      logic [Width-1:0]  fifo [Depth];
      logic [DepthW+2:0] wptr, rptr;

      // implements (++val) mod Depth
      function automatic logic [DepthW+2:0] modinc(logic [DepthW+2:0] val, int modval);
        if (val == Depth-1) return 0;
        else                return val + 1;
      endfunction

      // this only models the data flow, since the control logic is tested below
      always_ff @(posedge clk_i or negedge rst_ni) begin : p_fifo_model
        if (!rst_ni) begin
          wptr      <= 0;
          rptr      <= 0;
          ref_depth <= 0;
        end else begin
          if (clr_i) begin
            wptr      <= 0;
            rptr      <= 0;
            ref_depth <= 0;
          end else begin
            if (wvalid && wready && rvalid && rready) begin
              fifo[wptr] <= wdata;
              wptr <= modinc(wptr, Depth);
              rptr <= modinc(rptr, Depth);
            end else if (wvalid && wready) begin
              fifo[wptr] <= wdata;
              wptr <= modinc(wptr, Depth);
              ref_depth <= ref_depth + 1;
            end else if (rvalid && rready) begin
              rptr <= modinc(rptr, Depth);
              ref_depth <= ref_depth - 1;
            end
          end
        end
      end

      if (Pass) begin : gen_pass
        assign ref_rdata = (ref_depth == 0) ? wdata : fifo[rptr];
      end else begin : no_pass
        assign ref_rdata = fifo[rptr];
      end

    end

    // check the data
    `ASSERT(DataCheck_A, rvalid |-> rdata == ref_rdata, clk_i, !rst_ni)
    // check the depth
    `ASSERT(DepthCheck_A, ref_depth == depth, clk_i, !rst_ni)

  end

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // assert depth of FIFO
  `ASSERT(Depth_A, depth <= Depth, clk_i, !rst_ni)
  // if we clear the FIFO, it must be empty in the next cycle
  `ASSERT(CheckClrDepth_A, clr_i |=> depth == 0, clk_i, !rst_ni)
  // check write on full
  `ASSERT(WriteFull_A, depth == Depth && wvalid && !rready |=> depth == $past(depth),
      clk_i, !rst_ni || clr_i)
  // read empty
  `ASSERT(ReadEmpty_A, depth == 0 && rready && !wvalid |=> depth == 0,
      clk_i, !rst_ni || clr_i)

  // this is unreachable in depth 1 no-pass through mode
  if (Depth == 1 && Pass) begin : gen_d1_passthru
    // check simultaneous write and read
    `ASSERT(WriteAndRead_A, wready && wvalid && rvalid && rready |=> depth == $past(depth),
        clk_i, !rst_ni || clr_i)
  end

  if (Depth == 0) begin : gen_depth0
    // if there is no register, the FIFO is per definition pass-through
    `ASSERT_INIT(ZeroDepthNeedsPass_A, Pass == 1)
    // depth must remain zero
    `ASSERT(DepthAlwaysZero_A, depth == 0, clk_i, !rst_ni)
    // data is just passed through
    `ASSERT(DataPassThru_A, wdata == rdata, clk_i, !rst_ni)
    // FIFO is ready if downstream logic is ready
    `ASSERT(Wready_A, rready == wready, clk_i, !rst_ni)
    // valid input is valid output
    `ASSERT(Rvalid_A, rvalid == wvalid, clk_i, !rst_ni)
    // ensure full coverage
    `ASSERT(UnusedClr_A, prim_fifo_sync.gen_passthru_fifo.unused_clr == clr_i,
        clk_i, !rst_ni)
  end else begin : gen_depth_gt0
    // check wready
    `ASSERT(Wready_A, depth < Depth |-> wready, clk_i, !rst_ni)
    // check rvalid
    `ASSERT(Rvalid_A, depth > 0 |-> rvalid, clk_i, !rst_ni)
    // check write only
    `ASSERT(WriteOnly_A, wvalid && wready && !rready && depth < Depth |=>
        depth == $past(depth) + 1, clk_i, !rst_ni || clr_i)
    // check read only
    `ASSERT(ReadOnly_A, !wvalid && rready && rvalid && depth > 0 |=>
      depth == $past(depth) - 1, clk_i, !rst_ni || clr_i)
  end

  if (Pass) begin : gen_pass_fwd
    // if we clear the FIFO, it must be empty in the next cycle
    // but we may also get a pass through
    `ASSERT(CheckClrValid_A, clr_i |=> wvalid == rvalid, clk_i, !rst_ni)
  end else begin : gen_nopass_fwd
    // if we clear the FIFO, it must be empty in the next cycle
    `ASSERT(CheckClrValid_A, clr_i |=> !rvalid, clk_i, !rst_ni)
  end

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  if (Pass) begin : gen_pass_bkwd
    // there is still space in the FIFO or downstream logic is ready
    `ASSERT(WreadySpacekBkwd_A, wready |-> depth < Depth || rready, clk_i, !rst_ni)
    // elements ready to be read or upstream data is valid
    `ASSERT(RvalidElemskBkwd_A, rvalid |-> depth > 0 || wvalid, clk_i, !rst_ni)
  end else begin : gen_nopass_bkwd
    // there is still space in the FIFO
    `ASSERT(WreadySpacekBkwd_A, wready |-> depth < Depth, clk_i, !rst_ni)
    // elements ready to be read
    `ASSERT(RvalidElemskBkwd_A, rvalid |-> depth > 0, clk_i, !rst_ni)
  end

  // no more space in the FIFO
  `ASSERT(WreadyNoSpaceBkwd_A, !wready |-> depth == Depth, clk_i, !rst_ni)
  // elements ready to be read
  `ASSERT(RvalidNoElemskBkwd_A, !rvalid |-> depth == 0, clk_i, !rst_ni)

endmodule : prim_fifo_sync_assert_fpv
