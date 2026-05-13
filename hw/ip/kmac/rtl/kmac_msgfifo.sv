// Copyright lowRISC contributors (OpenTitan project).
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

  parameter  bit EnMasking = 1'b 1,
  localparam int Share     = (EnMasking) ? 2 : 1, // derived parameter

  // Internal MsgFIFO Entry count
  parameter  int MsgDepth = 9,
  localparam int MsgDepthW = $clog2(MsgDepth+1) // derived parameter
) (
  input clk_i,
  input rst_ni,

  // from REG or KeyMgr Intf input
  input  logic         fifo_valid_i,
  input [OutWidth-1:0] fifo_data_i[Share],
  input [OutWidth-1:0] fifo_strb_i,
  output logic         fifo_ready_o,
  input  logic         fifo_bypass_i,

  // MSG interface
  output logic                  msg_valid_o,
  output logic [OutWidth-1:0]   msg_data_o[Share],
  output logic [OutWidth/8-1:0] msg_strb_o,
  input  logic                  msg_ready_i,

  output logic                 fifo_empty_o,
  output logic                 fifo_full_o,
  output logic [MsgDepthW-1:0] fifo_depth_o,

  // Control
  input prim_mubi_pkg::mubi4_t clear_i,

  // When process_i is asserted, packer and FIFO are flushed. Once flushed, process_o is asserted.
  // When bypassing, nothing must be flushed.
  input  logic process_i,
  output logic process_o,

  err_t err_o
);

  //////////////////
  // Bypass logic //
  //////////////////
  // The packing and FIFO only support one share. These can be bypassed if operating with shares.
  logic                  fifo_valid;
  logic                  fifo_ready;
  logic [OutWidth/8-1:0] fifo_strb_byte;
  logic                  msg_valid;
  logic                  msg_ready;
  logic [OutWidth-1:0]   msg_data[Share];
  logic [OutWidth/8-1:0] msg_strb;

  // Reduce strobe from bit to byte level as KMAC core operates on byte strobes.
  always_comb begin
    fifo_strb_byte = '0;
    for (int i = 0; i < $bits(fifo_strb_byte); i++) begin
      fifo_strb_byte[i] = |fifo_strb_i[8 * i +: 8];
    end
  end

  assign fifo_valid   = fifo_bypass_i ? '0              : fifo_valid_i;
  assign fifo_ready_o = fifo_bypass_i ? msg_ready_i     : fifo_ready;
  assign msg_valid_o  = fifo_bypass_i ? fifo_valid_i    : msg_valid;
  assign msg_ready    = fifo_bypass_i ? '0              : msg_ready_i;
  assign msg_strb_o   = fifo_bypass_i ? fifo_strb_byte  : msg_strb;

  for (genvar i = 0; i < Share; i++) begin : g_msg_data_bypass_mux
    assign msg_data_o[i] = fifo_bypass_i ? fifo_data_i[i] : msg_data[i];
  end

  // If bypassing, packer and FIFO must not be flushed so we can gate the flush signal and
  // feed it directly to process_o.
  logic process_to_fifo;
  logic process_from_fifo;

  assign process_to_fifo = fifo_bypass_i ? '0        : process_i;
  assign process_o       = fifo_bypass_i ? process_i : process_from_fifo;

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
  logic packer_flush;
  logic packer_flush_done;
  logic msgfifo_flush_done;

  logic packer_err;

  assign packer_flush = process_to_fifo;

  // SEC_CM: PACKER.CTR.REDUN
  prim_packer #(
    .InW(OutWidth),
    .OutW(OutWidth),
    .HintByteData(1),

    // Turn on dup counter when EnMasking is set
    .EnProtection(EnMasking)
  ) u_packer (
    .clk_i,
    .rst_ni,

    .valid_i(fifo_valid),
    // FIFO operates only on one share
    .data_i (fifo_data_i[0]),
    .mask_i (fifo_strb_i),
    .ready_o(fifo_ready),

    .valid_o(packer_wvalid),
    .data_o (packer_wdata),
    .mask_o (packer_wmask),
    .ready_i(packer_wready),

    .flush_i     (packer_flush),
    .flush_done_o(packer_flush_done),

    .err_o(packer_err)
  );

  // Assign packer wdata and wmask to FIFO struct
  // In contrast to HMAC case, KMAC SHA3 operates in little-endian. MSG fifo is
  // converted into 3-D form so the endianness here is not a problem.
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

  assign msg_valid   = fifo_rvalid;
  assign fifo_rready = msg_ready;
  assign msg_strb    = fifo_rdata.strb;
  assign msg_data[0] = fifo_rdata.data;
  for (genvar i = 1; i < Share; i++) begin : g_msg_data_mask_assignment
    assign msg_data[i] = '0;
  end

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
        // Only enter packer-flush sequence when not in bypass mode.
        // In bypass mode, process_o is driven directly from process_i below.
        if (packer_flush) begin
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

  assign process_from_fifo = msgfifo_flush_done;

  err_t error;
  assign err_o = error;

  // Error assign
  always_comb begin : error_logic
    error = '{
      valid: 1'b 0,
      code: kmac_pkg::ErrNone,
      info: '0
    };

    // Priority case -> if .. else if
    if (packer_err) begin
      error = '{
        // If EnProtection is 0, packer_err is tied to 0
        valid: 1'b 1,
        code:  kmac_pkg::ErrPackerIntegrity,
        info:  kmac_pkg::ErrInfoW'(flush_st)
      };
    end else if (fifo_err) begin
      error = '{
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
  `ASSERT(PackerDoneDelay_A, $onehot0({packer_flush, packer_flush_done}))

  // process_i not asserted during the flush operation
  `ASSUME(PackerDoneValid_a, packer_flush |-> flush_st == FlushIdle)

  // No messages in between `process_i` and `clear_i`
  `ASSUME(MessageValid_a, fifo_valid_i |-> flush_st == FlushIdle)

`ifdef INC_ASSERT
  // INC_ASSERT is used to hide signal definitions that are only used for assertions.
  //VCS coverage off
  // pragma coverage off

  // Assert that fifo_bypass_i remains stable once the first messages was handshaked until the FIFO
  // has been flushed or the full message is sent downstream, respectively.
  logic first_data_entered;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      first_data_entered <= 1'b0;
    end else if (fifo_valid_i && fifo_ready_o) begin
      first_data_entered <= 1'b1;
    end else if (process_o) begin
      first_data_entered <= 1'b0;
    end
  end

  `ASSERT(BypassCtrlStable_A,
    first_data_entered && !process_o
    |-> fifo_bypass_i == $past(fifo_bypass_i))

`endif

endmodule
