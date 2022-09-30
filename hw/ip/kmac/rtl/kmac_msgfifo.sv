// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC MSG_FIFO
//
// This module converts TL-UL interface into MSG_FIFO interface used in KMAC.

`include "prim_assert.sv"

module kmac_msgfifo
  import kmac_pkg::*;
#(
  // OutWidth is MsgFIFO data width. prim_packer converts InW to OutW prior to
  // pushing to MsgFIFO
  parameter int OutWidth = 64,

  parameter bit EnMasking = 1'b 1,

  // Internal MsgFIFO Entry count
  parameter  int MsgDepth = 9,
  localparam int MsgDepthW = $clog2(MsgDepth+1) // derived parameter
) (
  input clk_i,
  input rst_ni,

  // from REG or KeyMgr Intf input
  input                fifo_valid_i,
  input [OutWidth-1:0] fifo_data_i,
  input [OutWidth-1:0] fifo_mask_i,
  output               fifo_ready_o,

  // MSG interface
  output logic                  msg_valid_o,
  output logic [OutWidth-1:0]   msg_data_o,
  output logic [OutWidth/8-1:0] msg_strb_o,
  input                         msg_ready_i,

  output logic                 fifo_empty_o,
  output logic                 fifo_full_o,
  output logic [MsgDepthW-1:0] fifo_depth_o,

  // Control
  input prim_mubi_pkg::mubi4_t clear_i,

  // process_i --> process_o
  // process_o asserted after all internal messages are flushed out to MSG interface
  input        process_i,
  output logic process_o,

  err_t err_o
);

  /////////////////
  // Definitions //
  /////////////////
  typedef struct packed {
    logic [OutWidth-1:0]   data;
    logic [OutWidth/8-1:0] strb; // one bit per byte
  } fifo_t;

  typedef enum logic [1:0] {
    // In Idle, it checks if process input received or not.
    // If received, the signal goes to packer and flush internal pending data
    FlushIdle,

    // In Packer state, it waits the packer flush operation completes.
    // The flush_done signal do nothing but after this, it is assumed that
    // MSG FIFO received the request.
    FlushPacker,

    // In Fifo, it waits until MsgFifo is empty. Then asserts process_o
    FlushFifo,

    // After flushing, it waits the done (clear) signal. It is assumed that
    // no incoming messages are transmitted between `process_i` and `clear_i`
    FlushClear
  } flush_st_e;

  /////////////
  // Signals //
  /////////////

  // Packer write path
  logic                packer_wvalid;
  logic [OutWidth-1:0] packer_wdata;
  logic [OutWidth-1:0] packer_wmask;
  logic                packer_wready;

  // Message FIFO signals
  logic  fifo_wvalid;
  fifo_t fifo_wdata;
  logic  fifo_wready;
  logic  fifo_rvalid;
  fifo_t fifo_rdata;
  logic  fifo_rready;

  logic fifo_err; // FIFO dup. counter error

  // packer flush to msg_fifo, then msg_fifo empty out the internals
  // then assert msgfifo_flush_done
  logic packer_flush_done;
  logic msgfifo_flush_done;

  logic packer_err;

  // SEC_CM: PACKER.CTR.REDUN
  prim_packer #(
    .InW          (OutWidth),
    .OutW         (OutWidth),
    .HintByteData (1),

    // Turn on dup counter when EnMasking is set
    .EnProtection (EnMasking)
  ) u_packer (
    .clk_i,
    .rst_ni,

    .valid_i      (fifo_valid_i),
    .data_i       (fifo_data_i),
    .mask_i       (fifo_mask_i),
    .ready_o      (fifo_ready_o),

    .valid_o      (packer_wvalid),
    .data_o       (packer_wdata),
    .mask_o       (packer_wmask),
    .ready_i      (packer_wready),

    .flush_i      (process_i),
    .flush_done_o (packer_flush_done),

    .err_o (packer_err)
  );

  // Assign packer wdata and wmask to FIFO struct
  // In contrast to HMAC case, KMAC SHA3 operates in little-endian. MSG fifo is
  // converted into 3-D form so the endianess here is not a problem.
  assign fifo_wdata.data = packer_wdata;
  always_comb begin
    fifo_wdata.strb = '0;
    for (int i = 0 ; i < OutWidth/8 ; i++) begin
      fifo_wdata.strb[i] = packer_wmask[8*i];
    end
  end

  // MsgFIFO
  prim_fifo_sync #(
    .Width  ($bits(fifo_t)),
    .Pass   (1'b 1),
    .Depth  (MsgDepth),
    .Secure (EnMasking)
  ) u_msgfifo (
    .clk_i,
    .rst_ni,
    .clr_i   (prim_mubi_pkg::mubi4_test_true_strict(clear_i)),

    .wvalid_i(fifo_wvalid),
    .wready_o(fifo_wready),
    .wdata_i (fifo_wdata),

    .rvalid_o (fifo_rvalid),
    .rready_i (fifo_rready),
    .rdata_o  (fifo_rdata),

    .full_o  (fifo_full_o),
    .depth_o (fifo_depth_o),
    .err_o   (fifo_err)

  );

  assign fifo_wvalid = packer_wvalid;
  assign packer_wready = fifo_wready;

  assign msg_valid_o = fifo_rvalid;
  assign fifo_rready = msg_ready_i;
  assign msg_data_o  = fifo_rdata.data;
  assign msg_strb_o  = fifo_rdata.strb;

  assign fifo_empty_o = !fifo_rvalid;

  // Flush (process from outside) handling
  flush_st_e flush_st, flush_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      flush_st <= FlushIdle;
    end else begin
      flush_st <= flush_st_d;
    end
  end

  always_comb begin
    flush_st_d = flush_st;

    msgfifo_flush_done = 1'b 0;

    unique case (flush_st)
      FlushIdle: begin
        if (process_i) begin
          flush_st_d = FlushPacker;
        end else begin
          flush_st_d = FlushIdle;
        end
      end

      FlushPacker: begin
        if (packer_flush_done) begin
          flush_st_d = FlushFifo;
        end else begin
          flush_st_d = FlushPacker;
        end
      end

      FlushFifo: begin
        if (fifo_empty_o) begin
          flush_st_d = FlushClear;

          msgfifo_flush_done = 1'b 1;
        end else begin
          flush_st_d = FlushFifo;
        end
      end

      FlushClear: begin
        if (prim_mubi_pkg::mubi4_test_true_strict(clear_i)) begin
          flush_st_d = FlushIdle;
        end else begin
          flush_st_d = FlushClear;
        end
      end

      default: begin
        flush_st_d = FlushIdle;
      end
    endcase
  end

  assign process_o = msgfifo_flush_done;

  // Error assign
  always_comb begin : error_logic
    err_o = '{
      valid: 1'b 0,
      code: kmac_pkg::ErrNone,
      info: '0
    };

    // Priority case -> if .. else if
    if (packer_err) begin
      err_o = '{
        // If EnProtection is 0, packer_err is tied to 0
        valid: 1'b 1,
        code:  kmac_pkg::ErrPackerIntegrity,
        info:  kmac_pkg::ErrInfoW'(flush_st)
      };
    end else if (fifo_err) begin
      err_o = '{
        valid: 1'b 1,
        code:  kmac_pkg::ErrMsgFifoIntegrity,
        info:  kmac_pkg::ErrInfoW'(flush_st)
      };
    end
  end : error_logic

  ////////////////
  // Assertions //
  ////////////////

  // Flush state known checker
  `ASSERT(FlushStInValid_A, flush_st inside {FlushIdle, FlushPacker, FlushFifo, FlushClear})

  // Packer done signal is asserted at least one cycle later
  `ASSERT(PackerDoneDelay_A, $onehot0({process_i, packer_flush_done}))

  // process_i not asserted during the flush operation
  `ASSUME(PackerDoneValid_a, process_i |-> flush_st == FlushIdle)

  // No messages in between `process_i` and `clear_i`
  `ASSUME(MessageValid_a, fifo_valid_i |-> flush_st == FlushIdle)

endmodule
