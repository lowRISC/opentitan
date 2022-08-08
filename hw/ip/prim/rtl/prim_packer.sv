// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Combine InW data and write to OutW data if packed to full word or stop signal

`include "prim_assert.sv"

// ICEBOX(#12958): Revise to send out the empty status.
module prim_packer #(
  parameter int unsigned InW  = 32,
  parameter int unsigned OutW = 32,

  // If 1, The input/output are byte granularity
  parameter int HintByteData = 0,

  // Turn on protect against FI for the pos variable
  parameter bit EnProtection = 1'b 0
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
  output logic            flush_done_o,

  // When EnProtection is set, err_o raises an error case (position variable
  // mismatch)
  output logic            err_o
);

  localparam int unsigned Width    = InW + OutW;  // storage width
  localparam int unsigned ConcatW  = Width + InW; // Input concatenated width
  localparam int unsigned PtrW     = $clog2(ConcatW+1);
  localparam int unsigned IdxW     = prim_util_pkg::vbits(InW);
  localparam int unsigned OnesCntW = $clog2(InW+1);

  logic valid_next, ready_next;
  logic [Width-1:0]   stored_data, stored_mask;
  logic [ConcatW-1:0] concat_data, concat_mask;
  logic [ConcatW-1:0] shiftl_data, shiftl_mask;
  logic [InW-1:0]     shiftr_data, shiftr_mask;

  logic [PtrW-1:0]     pos_q;         // Current write position
  logic [IdxW-1:0]     lod_idx;       // result of Leading One Detector
  logic [OnesCntW-1:0] inmask_ones;   // Counting Ones for mask_i

  logic ack_in, ack_out;

  logic flush_valid; // flush data out request
  logic flush_done;

  // Computing next position ==================================================
  always_comb begin
    // counting mask_i ones
    inmask_ones = '0;
    for (int i = 0 ; i < InW ; i++) begin
      inmask_ones = inmask_ones + OnesCntW'(mask_i[i]);
    end
  end

  logic [PtrW-1:0] pos_with_input;
  assign pos_with_input = pos_q + PtrW'(inmask_ones);

  if (EnProtection == 1'b 0) begin : g_pos_nodup
    logic [PtrW-1:0] pos_d;

    always_comb begin
      pos_d = pos_q;

      unique case ({ack_in, ack_out})
        2'b00: pos_d = pos_q;
        2'b01: pos_d = (int'(pos_q) <= OutW) ? '0 : pos_q - PtrW'(OutW);
        2'b10: pos_d = pos_with_input;
        2'b11: pos_d = (int'(pos_with_input) <= OutW) ? '0 : pos_with_input - PtrW'(OutW);
        default: pos_d = pos_q;
      endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        pos_q <= '0;
      end else if (flush_done) begin
        pos_q <= '0;
      end else begin
        pos_q <= pos_d;
      end
    end

    assign err_o = 1'b 0; // No checker logic

  end else begin : g_pos_dupcnt // EnProtection == 1'b 1
    // incr_en: Increase the pos by cnt_step. ack_in && !ack_out
    // decr_en: Decrease the pos by cnt_step. !ack_in && ack_out
    // set_en:  Set to specific value in case of ack_in && ack_out.
    //          This case, the value could be increased or descreased based on
    //          the input size (inmask_ones)
    logic            cnt_incr_en, cnt_decr_en, cnt_set_en;
    logic [PtrW-1:0] cnt_step, cnt_set;

    assign cnt_incr_en =  ack_in && !ack_out;
    assign cnt_decr_en = !ack_in &&  ack_out;
    assign cnt_set_en  =  ack_in &&  ack_out;

    // counter has underflow protection.
    assign cnt_step = (cnt_incr_en) ? PtrW'(inmask_ones) : PtrW'(OutW);

    always_comb begin : cnt_set_logic

      // default, consuming all data
      cnt_set = '0;

      if (pos_with_input > PtrW'(OutW)) begin
        // pos_q + inmask_ones is bigger than Output width. Still data remained.
        cnt_set = pos_with_input - PtrW'(OutW);
      end
    end : cnt_set_logic


    prim_count #(
      .Width      (PtrW),
      .ResetValue ('0  )
    ) u_pos (
      .clk_i,
      .rst_ni,

      .clr_i      (flush_done),

      .set_i      (cnt_set_en),
      .set_cnt_i  (cnt_set   ),

      .incr_en_i  (cnt_incr_en),
      .decr_en_i  (cnt_decr_en),
      .step_i     (cnt_step   ),

      .cnt_o      (pos_q     ), // Current counter state
      .cnt_next_o (          ), // Next counter state

      .err_o
    );
  end // g_pos_dupcnt

  //---------------------------------------------------------------------------

  // Leading one detector for mask_i
  always_comb begin
    lod_idx = 0;
    for (int i = InW-1; i >= 0 ; i--) begin
      if (mask_i[i] == 1'b1) begin
        lod_idx = IdxW'(unsigned'(i));
      end
    end
  end

  assign ack_in  = valid_i & ready_o;
  assign ack_out = valid_o & ready_i;

  // Data process =============================================================
  //  shiftr : Input data shifted right to put the leading one at bit zero
  assign shiftr_data = (valid_i) ? data_i >> lod_idx : '0;
  assign shiftr_mask = (valid_i) ? mask_i >> lod_idx : '0;

  //  shiftl : Input data shifted into the current stored position
  assign shiftl_data = ConcatW'(shiftr_data) << pos_q;
  assign shiftl_mask = ConcatW'(shiftr_mask) << pos_q;

  // concat : Merging stored and shiftl
  assign concat_data = {{(InW){1'b0}}, stored_data & stored_mask} |
                       (shiftl_data & shiftl_mask);
  assign concat_mask = {{(InW){1'b0}}, stored_mask} | shiftl_mask;

  logic [Width-1:0] stored_data_next, stored_mask_next;

  always_comb begin
    unique case ({ack_in, ack_out})
      2'b 00: begin
        stored_data_next = stored_data;
        stored_mask_next = stored_mask;
      end
      2'b 01: begin
        // ack_out : shift the amount of OutW
        stored_data_next = {{OutW{1'b0}}, stored_data[Width-1:OutW]};
        stored_mask_next = {{OutW{1'b0}}, stored_mask[Width-1:OutW]};
      end
      2'b 10: begin
        // ack_in : Store concat data
        stored_data_next = concat_data[0+:Width];
        stored_mask_next = concat_mask[0+:Width];
      end
      2'b 11: begin
        // both : shift the concat_data
        stored_data_next = concat_data[ConcatW-1:OutW];
        stored_mask_next = concat_mask[ConcatW-1:OutW];
      end
      default: begin
        stored_data_next = stored_data;
        stored_mask_next = stored_mask;
      end
    endcase
  end

  // Store the data temporary if it doesn't exceed OutW
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stored_data <= '0;
      stored_mask <= '0;
    end else if (flush_done) begin
      stored_data <= '0;
      stored_mask <= '0;
    end else begin
      stored_data <= stored_data_next;
      stored_mask <= stored_mask_next;
    end
  end
  //---------------------------------------------------------------------------

  // flush handling
  typedef enum logic {
    FlushIdle,
    FlushSend
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

    flush_valid = 1'b0;
    flush_done  = 1'b0;

    unique case (flush_st)
      FlushIdle: begin
        if (flush_i) begin
          flush_st_next = FlushSend;
        end else begin
          flush_st_next = FlushIdle;
        end
      end

      FlushSend: begin
        if (pos_q == '0) begin
          flush_st_next = FlushIdle;

          flush_valid = 1'b 0;
          flush_done  = 1'b 1;
        end else begin
          flush_st_next = FlushSend;

          flush_valid = 1'b 1;
          flush_done  = 1'b 0;
        end
      end
      default: begin
        flush_st_next = FlushIdle;

        flush_valid = 1'b 0;
        flush_done  = 1'b 0;
      end
    endcase
  end

  assign flush_done_o = flush_done;


  // Output signals ===========================================================
  assign valid_next = (int'(pos_q) >= OutW) ? 1'b 1 : flush_valid;

  // storage space is InW + OutW. So technically, ready_o can be asserted even
  // if `pos_q` is greater than OutW. But in order to do that, the logic should
  // use `inmask_ones` value whether pos_q+inmask_ones is less than (InW+OutW)
  // with `valid_i`. It creates a path from `valid_i` --> `ready_o`.
  // It may create a timing loop in some modules that use `ready_o` to
  // `valid_i` (which is not a good practice though)
  assign ready_next = int'(pos_q) <= OutW;

  // Output request
  assign valid_o = valid_next;
  assign data_o  = stored_data[OutW-1:0];
  assign mask_o  = stored_mask[OutW-1:0];

  // ready_o
  assign ready_o = ready_next;
  //---------------------------------------------------------------------------

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////
  // Assumption: mask_i should be contiguous ones
  // e.g: 0011100 --> OK
  //      0100011 --> Not OK
  if (InW > 1) begin : gen_mask_assert
    `ASSUME(ContiguousOnesMask_M,
            valid_i |-> $countones(mask_i ^ {mask_i[InW-2:0],1'b0}) <= 2)
  end

  // Flush and Write Enable cannot be asserted same time
  `ASSUME(ExFlushValid_M, flush_i |-> !valid_i)

  // While in flush state, new request shouldn't come
  `ASSUME(ValidIDeassertedOnFlush_M,
          flush_st == FlushSend |-> $stable(valid_i))

  // If not acked, input port keeps asserting valid and data
  `ASSUME(DataIStable_M,
          ##1 valid_i && $past(valid_i) && !$past(ready_o)
          |-> $stable(data_i) && $stable(mask_i))

  `ASSERT(FlushFollowedByDone_A,
          ##1 $rose(flush_i) && !flush_done_o |-> !flush_done_o [*0:$] ##1 flush_done_o)

  // If not acked, valid_o should keep asserting
  `ASSERT(ValidOPairedWidthReadyI_A,
          valid_o && !ready_i |=> valid_o)

  // If stored data is greater than the output width, valid should be asserted
  `ASSERT(ValidOAssertedForStoredDataGTEOutW_A,
          ($countones(stored_mask) >= OutW) |-> valid_o)

  // If output port doesn't accept the data, the data should be stable
  `ASSERT(DataOStableWhenPending_A,
          ##1 valid_o && $past(valid_o)
          && !$past(ready_i) |-> $stable(data_o))

  // If input data & stored data are greater than OutW, remained should be stored
  `ASSERT(ExcessiveDataStored_A,
          ack_in && ack_out && (($countones(mask_i) + $countones(stored_mask)) > OutW)
          |=> (($past(data_i) &  $past(mask_i)) >>
               ($past(lod_idx)+OutW-$countones($past(stored_mask))))
               == stored_data)

  `ASSERT(ExcessiveMaskStored_A,
          ack_in && ack_out && (($countones(mask_i) + $countones(stored_mask)) > OutW)
          |=> ($past(mask_i) >>
               ($past(lod_idx)+OutW-$countones($past(stored_mask))))
              == stored_mask)

  // Assertions for byte hint enabled
  if (HintByteData != 0) begin : g_byte_assert
    `ASSERT_INIT(InputDividedBy8_A,  InW  % 8 == 0)
    `ASSERT_INIT(OutputDividedBy8_A, OutW % 8 == 0)

    // Masking[8*i+:8] should be all zero or all one
    for (genvar i = 0 ; i < InW/8 ; i++) begin : g_byte_input_masking
      `ASSERT(InputMaskContiguous_A,
              valid_i |-> (|mask_i[8*i+:8] == 1'b 0)
                       || (&mask_i[8*i+:8] == 1'b 1))
    end
    for (genvar i = 0 ; i < OutW/8 ; i++) begin : g_byte_output_masking
      `ASSERT(OutputMaskContiguous_A,
              valid_o |-> (|mask_o[8*i+:8] == 1'b 0)
                       || (&mask_o[8*i+:8] == 1'b 1))
    end
  end
endmodule
