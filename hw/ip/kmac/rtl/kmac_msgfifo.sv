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
  parameter int InWidth = 32,   // 32 bit
  parameter int InDepth = 512 , // 2kB in space

  // OutWidth is MsgFIFO data width. prim_packer converts InW to OutW prior to
  // pushing to MsgFIFO
  parameter int OutWidth = 64,

  // Internal MsgFIFO Entry count
  parameter  int MsgDepth = 9,
  localparam int MsgDepthW = $clog2(MsgDepth+1) // derived parameter
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // MSG interface
  output logic                  msg_valid_o,
  output logic [OutWidth-1:0]   msg_data_o,
  output logic [OutWidth/8-1:0] msg_strb_o,
  input                         msg_ready_i,

  output logic                 fifo_empty_o,
  output logic                 fifo_full_o,
  output logic [MsgDepthW-1:0] fifo_depth_o,

  // Config
  // endian_swap converts little-endian to big-endian or vice versa
  input endian_swap_i,

  // Control
  input clear_i,

  // process_i --> process_o
  // process_o asserted after all internal messages are flushed out to MSG interface
  input        process_i,
  output logic process_o
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

  // TL-UL Adapter signals
  logic        tlram_req;
  logic        tlram_gnt;
  logic        tlram_we;
  logic [8:0]  tlram_addr;   // NOT_READ
  logic [31:0] tlram_wdata;
  logic [31:0] tlram_wmask;
  logic [31:0] tlram_rdata;
  logic        tlram_rvalid;
  logic [1:0]  tlram_rerror;
  logic [31:0] tlram_wdata_endian;
  logic [31:0] tlram_wmask_endian;

  // Tie the read path
  assign tlram_rvalid = 1'b 0;
  assign tlram_rdata = '0;
  assign tlram_rerror = '0;

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

  // packer flush to msg_fifo, then msg_fifo empty out the internals
  // then assert msgfifo_flush_done
  logic packer_flush_done;
  logic msgfifo_flush_done;

  // TL Adapter
  tlul_adapter_sram #(
    .SramAw ($clog2(InDepth)),
    .SramDw (InWidth),
    .Outstanding (1),
    .ByteAccess  (1),
    .ErrOnRead   (1)
  ) u_tlul_adapter (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .req_o    (tlram_req),
    .gnt_i    (tlram_gnt),
    .we_o     (tlram_we ),
    .addr_o   (tlram_addr),
    .wdata_o  (tlram_wdata),
    .wmask_o  (tlram_wmask),
    .rdata_i  (tlram_rdata),
    .rvalid_i (tlram_rvalid),
    .rerror_i (tlram_rerror)
  );

  // Convert endian here
  //    prim_packer always packs to the right, but SHA engine assumes incoming
  //    to be big-endian, [31:24] comes first. So, the data is reverted after
  //    prim_packer before the message fifo. here to reverse if not big-endian
  //    before pushing to the packer.
  assign tlram_wdata_endian = conv_endian32(tlram_wdata, ~endian_swap_i);
  assign tlram_wmask_endian = conv_endian32(tlram_wmask, ~endian_swap_i);

  prim_packer #(
    .InW      (InWidth),
    .OutW     (OutWidth)
  ) u_packer (
    .clk_i,
    .rst_ni,

    .valid_i      (tlram_req & tlram_we),
    .data_i       (tlram_wdata_endian),
    .mask_i       (tlram_wmask_endian),
    .ready_o      (tlram_gnt),

    .valid_o      (packer_wvalid),
    .data_o       (packer_wdata),
    .mask_o       (packer_wmask),
    .ready_i      (packer_wready),

    .flush_i      (process_i),
    .flush_done_o (packer_flush_done)
  );

  // Convert packer wdata and wmask to FIFO struct
  // As packer packs to right, it converts the data here again
  // TODO: Is it true internal SHA3 is big-endian same as HMAC?
  assign fifo_wdata.data = conv_endian64(packer_wdata, 1'b1);
  always_comb begin
    for (int i = 0 ; i < OutWidth/8 ; i++) begin
      fifo_wdata.strb[i] = packer_wmask[OutWidth/8-1 - i];
    end
  end

  // MsgFIFO
  prim_fifo_sync #(
    .Width ($bits(fifo_t)),
    .Pass  (1'b 1),
    .Depth (MsgDepth)
  ) u_msgfifo (
    .clk_i,
    .rst_ni,
    .clr_i   (clear_i),

    .wvalid_i(fifo_wvalid),
    .wready_o(fifo_wready),
    .wdata_i (fifo_wdata),

    .depth_o (fifo_depth_o),

    .rvalid_o (fifo_rvalid),
    .rready_i (fifo_rready),
    .rdata_o  (fifo_rdata)
  );

  assign fifo_wvalid = packer_wvalid;
  assign packer_wready = fifo_wready;

  assign msg_valid_o = fifo_rvalid;
  assign fifo_rready = msg_ready_i;
  assign msg_data_o  = fifo_rdata.data;
  assign msg_strb_o  = fifo_rdata.strb;

  assign fifo_empty_o = fifo_depth_o == '0;
  assign fifo_full_o  = fifo_depth_o == MsgDepth;

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
    flush_st_d = FlushIdle;

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
        if (clear_i) begin
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
  `ASSUME(MessageValid_a, tlram_req && tlram_we |-> flush_st == FlushIdle)

endmodule

