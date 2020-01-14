// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Combine InW data and write to OutW data if packed to full word or stop signal

`include "prim_assert.sv"

module prim_packer #(
  parameter int InW  = 32,
  parameter int OutW = 32
) (
  input clk_i ,
  input rst_ni,

  input                   valid_i,
  input        [InW-1:0]  data_i,
  input        [InW-1:0]  mask_i,
  output                  ready_o,

  output logic            valid_o,
  output logic [OutW-1:0] data_o,
  output logic [OutW-1:0] mask_o,
  input                   ready_i,

  input                   flush_i,  // If 1, send out remnant and clear state
  output logic            flush_done_o
);

  localparam int Width = InW + OutW;
  localparam int PtrW = $clog2(Width+1);
  localparam int MaxW = (InW > OutW) ? InW : OutW;

  logic valid_next, ready_next;
  logic [MaxW-1:0]  stored_data, stored_mask;
  logic [Width-1:0] concat_data, concat_mask;
  logic [Width-1:0] shiftl_data, shiftl_mask;

  logic [PtrW-1:0]        pos, pos_next; // Current write position
  logic [$clog2(InW)-1:0] lod_idx;       // result of Leading One Detector
  logic [$clog2(InW+1)-1:0] inmask_ones;   // Counting Ones for mask_i

  logic ack_in, ack_out;

  logic flush_ready; // flush_i is pulse, so only when the output is ready flush_ready assets

  // Computing next position
  always_comb begin
    // counting mask_i ones
    inmask_ones = '0;
    for (int i = 0 ; i < InW ; i++) begin
      inmask_ones = inmask_ones + mask_i[i];
    end
  end

  assign pos_next = (valid_i) ? pos + PtrW'(inmask_ones) : pos;  // pos always stays (% OutW)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pos <= '0;
    end else if (flush_ready) begin
      pos <= '0;
    end else if (ack_out) begin
      `ASSERT_I(pos_next_gte_outw_p, pos_next >= OutW)
      pos <= pos_next - OutW;
    end else if (ack_in) begin
      pos <= pos_next;
    end
  end

  // Leading one detector for mask_i
  always_comb begin
    lod_idx = 0;
    for (int i = InW-1; i >= 0 ; i--) begin
      if (mask_i[i] == 1'b1) begin
        lod_idx = i;
      end
    end
  end

  assign ack_in  = valid_i & ready_o;
  assign ack_out = valid_o & ready_i;

  // Data process
  assign shiftl_data = (valid_i) ? Width'(data_i >> lod_idx) << pos : '0;
  assign shiftl_mask = (valid_i) ? Width'(mask_i >> lod_idx) << pos : '0;
  assign concat_data = {{(Width-MaxW){1'b0}}, stored_data & stored_mask} |
                       (shiftl_data & shiftl_mask);
  assign concat_mask = {{(Width-MaxW){1'b0}}, stored_mask} | shiftl_mask;

  logic [MaxW-1:0] stored_data_next, stored_mask_next;

  if (InW >= OutW) begin : gen_stored_in
    assign stored_data_next = concat_data[OutW+:InW];
    assign stored_mask_next = concat_mask[OutW+:InW];
  end else begin : gen_stored_out
    assign stored_data_next = {{(OutW-InW){1'b0}}, concat_data[OutW+:InW]};
    assign stored_mask_next = {{(OutW-InW){1'b0}}, concat_mask[OutW+:InW]};
  end

  // Store the data temporary if it doesn't exceed OutW
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stored_data <= '0;
      stored_mask <= '0;
    end else if (flush_ready) begin
      stored_data <= '0;
      stored_mask <= '0;
    end else if (ack_out) begin
      stored_data <= stored_data_next;
      stored_mask <= stored_mask_next;
    end else if (ack_in) begin
      // When the requested size is smaller than OutW or output isn't ready
      // Assume when output isn't ready, the module  holds the input request
      stored_data <= concat_data[MaxW-1:0];
      stored_mask <= concat_mask[MaxW-1:0];
    end
  end

  // flush_ready handling
  typedef enum logic {
    FlushIdle,
    FlushWait
  } flush_st_e;
  flush_st_e flush_st, flush_st_next;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      flush_st <= FlushIdle;
    end else begin
      flush_st <= flush_st_next;
    end
  end

  always_comb begin
    flush_st_next = FlushIdle;

    flush_ready = 1'b0;

    unique case (flush_st)
      FlushIdle: begin
        if (flush_i && !ready_i) begin
          // Wait until hold released
          flush_st_next = FlushWait;

          flush_ready = 1'b0;
        end else if (flush_i && ready_i) begin
          // Can write right away!
          flush_st_next = FlushIdle;

          flush_ready = 1'b1;
        end else begin
          flush_st_next = FlushIdle;
        end
      end

      FlushWait: begin
        // TODO: Add timeout and force flush
        if (ready_i) begin
          // Ready to write
          flush_st_next = FlushIdle;

          flush_ready = 1'b1;
        end else begin
          // Wait ...
          flush_st_next = FlushWait;

          flush_ready = 1'b0;
        end
      end

      default: begin
        flush_st_next = FlushIdle;

        flush_ready = 1'b0;
      end
    endcase
  end

  assign flush_done_o = flush_ready;

  assign valid_next = (pos_next >= OutW) ? 1'b 1 : flush_ready & (pos != '0);
  assign ready_next = ack_out ? 1'b1 : pos_next <= MaxW; // New `we` needs to be hold.

  // Output request
  assign valid_o = valid_next;
  assign data_o  = concat_data[OutW-1:0];
  assign mask_o  = concat_mask[OutW-1:0];

  // ready_o
  assign ready_o = ready_next;

  // TODO: Implement Pipelined logic
  //       Need to change pos logic, mask&data calculation logic too

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////
  // Assumption: mask_i should be contiguous ones
  // e.g: 0011100 --> OK
  //      0100011 --> Not OK
  `ASSUME(ContiguousOnesMask_M,
          valid_i |-> $countones(mask_i ^ {mask_i[InW-2:0],1'b0}) <= 2)

  // Assume data pattern to reduce FPV test time
  //`ASSUME_FPV(FpvDataWithin_M,
  //            data_i inside {'0, '1, 32'hDEAD_BEEF},
  //            clk_i, !rst_ni)

  // Flush and Write Enable cannot be asserted same time
  `ASSUME(ExFlushValid_M, flush_i |-> !valid_i)

  // While in flush state, new request shouldn't come
  `ASSUME(ValidIDeassertedOnFlush_M,
          flush_st == FlushWait |-> $stable(valid_i))

  // If not acked, input port keeps asserting valid and data
  `ASSUME(DataIStable_M,
          ##1 valid_i && $past(valid_i) && !$past(ready_o)
          |-> $stable(data_i) && $stable(mask_i))
  `ASSUME(ValidIPairedWithReadyO_M,
          valid_i && !ready_o |=> valid_i)

  `ASSERT(FlushFollowedByDone_A,
          ##1 $rose(flush_i) && !flush_done_o |-> !flush_done_o [*0:$] ##1 flush_done_o)

  // If not acked, valid_o should keep asserting
  `ASSERT(ValidOPairedWidthReadyI_A,
          valid_o && !ready_i |=> valid_o)

  // If input mask + stored data is greater than output width, valid should be asserted
  `ASSERT(ValidOAssertedForInputGTEOutW_A,
          valid_i && (($countones(mask_i) + $countones(stored_mask)) >= OutW) |-> valid_o)

  // If output port doesn't accept the data, the data should be stable
  `ASSERT(DataOStableWhenPending_A,
          ##1 valid_o && $past(valid_o)
          && !$past(ready_i) |-> $stable(data_o))

  // If input data & stored data are greater than OutW, remained should be stored
  // TODO: Find out how the FPV time can be reduced.
  //`ASSERT(ExcessiveDataStored_A,
  //        ack_in && (($countones(mask_i) + $countones(stored_mask)) > OutW) |=>
  //          (($past(data_i) &  $past(mask_i)) >>
  //          ($past(lod_idx)+OutW-$countones($past(stored_mask))))
  //          == stored_data,
  //        clk_i, !rst_ni)
  `ASSERT(ExcessiveMaskStored_A,
          ack_in && (($countones(mask_i) + $countones(stored_mask)) > OutW) |=>
          ($past(mask_i) >>
          ($past(lod_idx)+OutW-$countones($past(stored_mask))))
            == stored_mask)

endmodule
