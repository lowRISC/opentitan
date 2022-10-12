// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Device Flash Read command SRAM request/rsp

/*
  spid_readsram module is a submodule of the read command process block. Its
  main purpose is to manage the SRAM request address and returning of the data
  in a spi_byte_t size.

  The sequence is:

  1. read FSM sends the buffer fill request.
  2. this logic sends the SRAM request based on the current address.
  3. when it returns, based on the current address, the internal FSM pushes
     data into the FIFO. It means, the FIFO push happens when addr[0] is
     received.
  4. If the available depth becomes 4, the logic increases the address
     ({current_address_i[31:2] + 1'b 1, 2'b00}) and sends another SRAM read
     request.
*/
`include "prim_assert.sv"

module spid_readsram
  import spi_device_pkg::*;
#(
  // Read command configurations
  // Base address: Index of DPSRAM
  // Buffer size: # of indices assigned to Read Buffer.
  //    This is used to calculate double buffering and threshold.
  parameter sram_addr_t  ReadBaseAddr    = spi_device_pkg::SramReadBufferIdx,
  parameter int unsigned ReadBufferDepth = spi_device_pkg::SramMsgDepth,

  // Mailbox Base Addr: Beginning Index of Mailbox in DPSRAM
  // Mailbox Size: Mailbox buffer size (# of indices)
  parameter sram_addr_t  MailboxBaseAddr = spi_device_pkg::SramMailboxIdx,
  parameter int unsigned MailboxDepth    = spi_device_pkg::SramMailboxDepth,

  // SFDP Base Addr: the beginning index of the SFDP region in DPSRAM
  // SFDP Depth: The size of the SFDP buffer (64 fixed in the spi_device_pkg)
  parameter sram_addr_t  SfdpBaseAddr    = spi_device_pkg::SramSfdpIdx,
  parameter int unsigned SfdpDepth       = spi_device_pkg::SramSfdpDepth
) (
  input clk_i,      // SCK
  input rst_ni,     // CSb

  input sram_read_req_i, // from FSM

  // addr_latched_i
  //        _________ _________
  // ADDR: X addr[1] X addr[0] >----
  //             _________
  // sig:  _____/         \_________
  input addr_latched_i,  // indicator of addr[1] -> addr[0]

  // current_address_i is the address pointer the byte sent to the host system.
  // If it is the first request of the command, then the current_address_i is
  // the latched address field.
  input [31:0] current_address_i,

  input        mailbox_en_i,
  input [31:0] mailbox_addr_i,

  input sfdp_hit_i,    // selected DP is DpReadSFDP

  // SRAM request and response
  output sram_l2m_t sram_l2m_o,
  input  sram_m2l_t sram_m2l_i,

  // FIFO output (spi_byte_t)
  output logic      fifo_rvalid_o,
  input             fifo_rready_i,
  output spi_byte_t fifo_rdata_o
);


  ////////////////
  // Definition //
  ////////////////

  // States
  typedef enum logic [1:0] {
    StIdle, // Reset state, waits sram_read_req
    StPush, // With returned data, push the data into spi_byte_t fifo
    StActive // Now in the middle of the process. Sits here
  } st_e;
  st_e st_q, st_d;

  typedef enum logic {
    AddrInput,     // Received command address
    AddrContinuous // Continuous Read
  } addr_sel_e;
  addr_sel_e addr_sel;

  localparam int unsigned ReadBufAw = $clog2(ReadBufferDepth);
  localparam int unsigned MailboxAw = $clog2(MailboxDepth);
  localparam int unsigned SfdpAw    = $clog2(SfdpDepth);

  ////////////
  // Signal //
  ////////////

  // mailbox_hit: it compares the next_address with mailbox space.
  logic mailbox_hit;

  // State Machine output

  // data_inc: incoming data is word size (sram_data_t).
  // FIFO size is spi_byte_t. So, only a byte can be pushed to the FIFO at
  // a time. data_inc to increase the index to next
  logic data_inc;

  // strb_set: When addr[0] phase, strb_set is 1 (by FSM). This is to latch
  // the offset of the received address. The offset is used to push to the
  // FIFO only for the required bytes.
  logic strb_set;
  assign strb_set = addr_latched_i;

  logic [31:0] next_address;

  logic sram_req;
  assign sram_l2m_o.req   = sram_req;
  assign sram_l2m_o.we    = 1'b 0;
  assign sram_l2m_o.wdata = '0;
  assign sram_l2m_o.wstrb = 8'h0; // no write

  sram_addr_t sram_addr;
  assign sram_l2m_o.addr = sram_addr;

  sram_data_t sram_data;

  // FIFO
  logic fifo_wvalid, fifo_wready;
  spi_byte_t fifo_wdata;

  logic sram_d_valid, sram_d_ready;
  logic sram_fifo_full;
  logic unused_sram_depth;

  // Unused
  logic unused_fifo_full;
  logic [1:0] unused_fifo_depth;

  logic unused_next_address;
  assign unused_next_address = ^{next_address[31:$bits(sram_addr_t)+1],next_address[1:0]};

  //////////////
  // Datapath //
  //////////////

  // Mailbox hit detection
  // mailbox_hit_i only checks current_address_i.
  // SRAM logic sends request to the next address based on the condition.
  // Need to check the mailbox hit based on the SRAM address rather than
  // current_address.
  localparam logic [31:0] MailboxMask = {{30-MailboxAw{1'b1}}, {2+MailboxAw{1'b0}}};

  logic [31:0] mailbox_masked_addr;
  assign mailbox_masked_addr = (next_address & MailboxMask);
  assign mailbox_hit         = mailbox_en_i
                             && (mailbox_masked_addr == mailbox_addr_i);

  logic sram_latched; // sram request sent
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sram_latched <= 1'b 0;
    else if (sram_req) sram_latched <= 1'b 1;
  end

  logic [1:0] strb;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) strb <= 2'b 00;
    else if (data_inc) strb <= strb + 1'b 1; // Overflow is OK
    else if (strb_set) strb <= current_address_i[1:0];
  end

  // fifo_wdata
  always_comb begin
    unique case (strb)
      2'b 00:  fifo_wdata = sram_data[ 7: 0];
      2'b 01:  fifo_wdata = sram_data[15: 8];
      2'b 10:  fifo_wdata = sram_data[23:16];
      2'b 11:  fifo_wdata = sram_data[31:24];
      default: fifo_wdata = '0;
    endcase
  end

  // Address calculation
  assign next_address = (addr_sel == AddrContinuous)
                      ? {current_address_i[31:2] + 1'b1, 2'b00}
                      : current_address_i;

  // Sram Address
  always_comb begin
    if (sfdp_hit_i) begin
      sram_addr = SfdpBaseAddr | sram_addr_t'(next_address[2+:SfdpAw]);
    end else if (mailbox_hit) begin
      sram_addr = MailboxBaseAddr | sram_addr_t'(next_address[2+:MailboxAw]);
    end else begin
      sram_addr = ReadBaseAddr | sram_addr_t'(next_address[2+:ReadBufAw]);
    end
  end

  ///////////////////
  // State Machine //
  ///////////////////

  /*
       _   _   _   _   _
  SCK | |_| |_| |_| |_| |_|
         ___ ___ ___ ___
  ADDR  X___X___X___X___X
          3   2   1   0
           ___
  S.RE    /   \__________
               ___
  S.R.V  _____/   \______

  STRB              / V \

  State  Idle X P   X Push
  */

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StIdle;
    else         st_q <= st_d;
  end

  always_comb begin
    st_d = st_q;

    fifo_wvalid = 1'b 0;

    addr_sel = AddrInput;
    data_inc = 1'b 0;

    sram_req = 1'b 0;
    sram_d_ready = 1'b 0;

    unique case (st_q)
      StIdle: begin
        addr_sel = AddrInput;

        if (sram_read_req_i) begin
          sram_req = 1'b 1;
        end

        if ((sram_read_req_i || sram_latched) && strb_set) begin
          // Regardless of permitted or not, FSM moves to StPush.
          // If not permitted, FSM will psh garbage data to the FIFO
          st_d = StPush;
        end else begin
          st_d = StIdle;
        end
      end

      StPush: begin
        if (sram_d_valid) begin
          fifo_wvalid = 1'b 1; // push to FIFO
        end

        if (fifo_wready) data_inc = 1'b 1;

        if (strb == 2'b 11 && fifo_wready) begin
          // pushed all bytes to FIFO
          st_d = StActive;

          sram_d_ready = 1'b 1;
        end else begin
          st_d = StPush;
        end
      end

      StActive: begin
        // Assume the SRAM logic is faster than update of current_address_i.
        // TODO: Put assertion.
        addr_sel = AddrContinuous; // Pointing to next_address to check mailbox hit
        if (!sram_fifo_full) begin
          st_d = StPush;

          sram_req = 1'b 1;
        end else begin
          st_d = StActive;
        end
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  //////////////
  // Instance //
  //////////////
  prim_fifo_sync #(
    .Width ($bits(sram_data_t)),
    .Pass  (1'b 1),
    .Depth (1),
    .OutputZeroIfEmpty (1'b 0)
  ) u_sram_fifo (
    .clk_i,
    .rst_ni,

    .clr_i (1'b 0),

    .wvalid_i (sram_m2l_i.rvalid),
    .wready_o (),
    .wdata_i  (sram_m2l_i.rdata),

    .rvalid_o (sram_d_valid),
    .rready_i (sram_d_ready),
    .rdata_o  (sram_data),

    .full_o   (sram_fifo_full),
    .depth_o  (unused_sram_depth),
    .err_o    ()
  );

  prim_fifo_sync #(
    .Width             ($bits(spi_byte_t)),
    .Pass              (1'b1),
    .Depth             (2),
    .OutputZeroIfEmpty (1'b0)
  ) u_fifo (
    .clk_i,
    .rst_ni,

    .clr_i    (1'b 0),

    .wvalid_i (fifo_wvalid),
    .wready_o (fifo_wready), // always assume empty space
    .wdata_i  (fifo_wdata ),

    .rvalid_o (fifo_rvalid_o),
    .rready_i (fifo_rready_i),
    .rdata_o  (fifo_rdata_o ),

    .full_o   (unused_fifo_full ),
    .depth_o  (unused_fifo_depth),
    .err_o    ()
  );

  // TODO: Handle SRAM integrity errors
  sram_err_t unused_sram_rerror;
  assign unused_sram_rerror = sram_m2l_i.rerror;


  ////////////////
  // Assertions //
  ////////////////

  // sfdp_hit keeps high until CSb de-assertion

  // mailbox_hit keeps high until CSb de-assertion

  // current_address keeps increasing (by word? or by byte) after receiving
  // sram_req

  // FIFO should not overflow. The Main state machine shall send request only
  // when it needs the data within 2 cycles
  `ASSERT(NotOverflow_A, sram_l2m_o.req && !sram_l2m_o.we |-> !sram_fifo_full)

  // SRAM access always read
  `ASSERT(SramReadOnly_A, sram_l2m_o.req |-> !sram_l2m_o.we)

  // SRAM data should return in next cycle
  `ASSUME(SramDataReturnRequirement_M, sram_l2m_o.req && !sram_l2m_o.we |=> sram_m2l_i.rvalid)

  // in fifo_pop, FIFO should not be empty for permitted operations.
  `ASSERT(FifoNotEmpty_A,
          fifo_rready_i |-> unused_fifo_depth != 0)

  // strb_set is asserted together with sram_req or follows the req
  `ASSUME(ReqStrbRelation_M, sram_read_req_i |-> ##[0:2] addr_latched_i)

  // Address latched signal is a pulse signal
  `ASSUME(AddrLatchedPulse_M, addr_latched_i |=> !addr_latched_i)

endmodule : spid_readsram
