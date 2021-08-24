// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash, Command Upload handler
/*
  This module uploads the incoming SPI transaction into DPSRAM. The logic
  parses the transaction into three fields -- opcode, address, and payload.
  This module uploads the fields into the FIFOs and the Payload buffer.

  cmdparse enables the upload submodule at the 7th negedge of SCK unlike other
  submodules (Readcmd, Status, Jedec are enabled when 8th posedge of SCK).
  cmdparse enables the upload module earlier to update the DPSRAM for 1 byte
  SPI command such as Chip Erase, Write Enable/Disable. The longest path is
  from parsing opcode, checking the upload bit in the cmd_info, then issuing
  the SRAM write request along with increasing cmd_fifo pointer by 1.

  The timing can be optimized in the cmdparse module to not check the opcode
  at once but maintaining the comparison bit fields [NumCmdInfo-1:0] in each
  beat of opcode. Eventually at 7th cycle, only two bits in the bit field are
  one at most unless the SW configures multiple cmd_info slot to have the same
  opcode. Then at the 8th beat, the logic only checks the last bit of opcode
  in the two cmd_info slot. The scheme reduces 8bit compare then
  log(NumCmdInfo) depth into one bit compare and 1 depth tree.
*/

`include "prim_assert.sv"

module spid_upload
  import spi_device_pkg::*;
#(
  parameter sram_addr_t  CmdFifoBaseAddr  = spi_device_pkg::SramCmdFifoIdx,
  parameter int unsigned CmdFifoDepth     = spi_device_pkg::SramCmdFifoDepth,

  parameter sram_addr_t  AddrFifoBaseAddr = spi_device_pkg::SramAddrFifoIdx,
  parameter int unsigned AddrFifoDepth    = spi_device_pkg::SramAddrFifoDepth,

  parameter sram_addr_t  PayloadBaseAddr  = spi_device_pkg::SramPayloadIdx,
  parameter int unsigned PayloadDepth     = spi_device_pkg::SramPayloadDepth,

  // SramAw, SramDw from spi_device_pkg
  parameter int unsigned SpiByte = $bits(spi_byte_t),

  // derived
  localparam int unsigned CmdPtrW  = $clog2(CmdFifoDepth+1),
  localparam int unsigned AddrPtrW = $clog2(AddrFifoDepth+1),

  localparam int unsigned PayloadByte = PayloadDepth * (SramDw/SpiByte),
  localparam int unsigned PayloadPtrW = $clog2(PayloadByte+1)
) (
  input clk_i,
  input rst_ni,

  input sys_clk_i,
  input sys_rst_ni,

  input sys_csb_deasserted_pulse_i,

  input sel_datapath_e sel_dp_i,

  // Sram access: (CMDFIFO/ ADDRFIFO/ PAYLOADBUFFER)
  output sram_l2m_t sck_sram_o,
  input  sram_m2l_t sck_sram_i,

  // SRAM access in sys_clk (CMDFIFO/ ADDRFIFO)
  // Arbiter among these + SW access is in the SPID top module
  output sram_l2m_t sys_cmdfifo_sram_o,
  input  sram_m2l_t sys_cmdfifo_sram_i,
  output sram_l2m_t sys_addrfifo_sram_o,
  input  sram_m2l_t sys_addrfifo_sram_i,

  // FIFO access in sys_clk (CMDFIFO/ ADDRFIFO)
  output logic       sys_cmdfifo_rvalid_o,
  input              sys_cmdfifo_rready_i,
  output logic [7:0] sys_cmdfifo_rdata_o,

  output logic        sys_addrfifo_rvalid_o,
  input               sys_addrfifo_rready_i,
  output logic [31:0] sys_addrfifo_rdata_o,

  // Interface: SPI to Parallel
  input               s2p_valid_i,
  input spi_byte_t    s2p_byte_i,
  input [BitCntW-1:0] s2p_bitcnt_i,

  // Interface: Parallel to SPI
  // Not used in spid_upload
  output logic      p2s_valid_o,
  output spi_byte_t p2s_data_o,
  input  logic      p2s_sent_i,

  // Configurations:
  input spi_mode_e spi_mode_i,

  input logic cfg_addr_4b_en_i,

  input cmd_info_t              cmd_info_i,
  input logic [CmdInfoIdxW-1:0] cmd_info_idx_i,

  output io_mode_e io_mode_o,

  output logic set_busy_o,

  output logic sys_cmdfifo_notempty_o,
  output logic sys_cmdfifo_full_o,
  output logic sys_addrfifo_notempty_o,
  output logic sys_addrfifo_full_o,

  output logic [CmdPtrW-1:0]     sys_cmdfifo_depth_o,
  output logic [AddrPtrW-1:0]    sys_addrfifo_depth_o,
  output logic [PayloadPtrW-1:0] sys_payload_depth_o
);

  localparam int unsigned CmdFifoWidth  =  8;
  localparam int unsigned AddrFifoWidth = 32;

  assign io_mode_o = SingleIO; // Only single input mode is supported in upload

  // Upload works in Flash and Passthrough both.
  spi_mode_e unused_spi_mode;
  assign unused_spi_mode = spi_mode_i;

  assign p2s_valid_o = 1'b 0;
  assign p2s_data_o  = '0;

  logic unused_p2s_sent;
  assign unused_p2s_sent = p2s_sent_i;

  ////////////////
  // Definition //
  ////////////////
  typedef enum int unsigned {
    SramCmdFifo  = 0,
    SramAddrFifo = 1,
    SramPayload  = 2
  } sramintf_e;
  localparam int unsigned NumSramIntf = 3;

  typedef enum logic [1:0] {
    StIdle,
    StAddress,
    StPayload
  } st_e;
  st_e st_q, st_d;

  ////////////
  // Signal //
  ////////////

  // SRAM access (to SRAM Arbiter)
  logic [NumSramIntf-1:0] sck_sram_req;
  logic [NumSramIntf-1:0] sck_sram_gnt;
  logic [NumSramIntf-1:0] sck_sram_write;
  logic [SramAw-1:0]      sck_sram_addr   [NumSramIntf];
  logic [SramDw-1:0]      sck_sram_wdata  [NumSramIntf];
  logic [SramDw-1:0]      sck_sram_wmask  [NumSramIntf];
  logic [NumSramIntf-1:0] sck_sram_rvalid; // not used
  logic [SramDw-1:0]      sck_sram_rdata  [NumSramIntf]; // not used
  logic [1:0]             sck_sram_rerror [NumSramIntf]; // not used

  logic [NumSramIntf-2:0] sys_sram_req;
  logic [NumSramIntf-2:0] sys_sram_gnt;
  logic [NumSramIntf-2:0] sys_sram_write;
  logic [SramAw-1:0]      sys_sram_addr   [NumSramIntf-1];
  logic [SramDw-1:0]      sys_sram_wdata  [NumSramIntf-1];
  logic [SramDw-1:0]      sys_sram_wmask  [NumSramIntf-1];
  logic [NumSramIntf-2:0] sys_sram_rvalid; // not used
  logic [SramDw-1:0]      sys_sram_rdata  [NumSramIntf-1]; // not used
  logic [1:0]             sys_sram_rerror [NumSramIntf-1]; // not used

  logic        cmdfifo_wvalid;
  logic        cmdfifo_wready; // Assume always ready
  logic [7:0]  cmdfifo_wdata ;
  logic        addrfifo_wvalid;
  logic        addrfifo_wready; // Assume always ready
  logic [31:0] addrfifo_wdata ;
  logic        payload_wvalid;
  logic        payload_wready; // Assume always ready
  logic [7:0]  payload_wdata ;

  // Unused wready
  logic unused_fifo_wready;
  assign unused_fifo_wready = ^{cmdfifo_wready, addrfifo_wready, payload_wready};

  // Simplified command info
  logic cmdinfo_addr_en, cmdinfo_addr_4b_en;

  logic unused_cmdinfo;
  assign unused_cmdinfo = ^{
    cmd_info_i.addr_swap_en,
    cmd_info_i.dummy_en,
    cmd_info_i.dummy_size,
    cmd_info_i.mbyte_en,
    cmd_info_i.opcode,
    cmd_info_i.payload_dir,
    cmd_info_i.payload_en,
    cmd_info_i.upload
  };

  // Address latch
  logic addr_update, addr_shift;
  logic [31:0] address_q, address_d;
  logic [4:0]  addrcnt;


  // unused
  logic unused_s2p_bitcnt;
  assign unused_s2p_bitcnt = ^s2p_bitcnt_i;

  logic unused_cmdinfo_idx;
  assign unused_cmdinfo_idx = ^cmd_info_idx_i;

  //////////////
  // Datapath //
  //////////////

  // Command info process
  assign cmdinfo_addr_en = cmd_info_i.addr_en;

  assign cmdinfo_addr_4b_en = spi_device_pkg::is_cmdinfo_addr_4b(
                              cmd_info_i, cfg_addr_4b_en_i);

  assign cmdfifo_wdata  = s2p_byte_i; // written to FIFO at first
  assign addrfifo_wdata = address_d;
  assign payload_wdata  = s2p_byte_i;

  // Address counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)          addrcnt <= '0;
    else if (addr_update) addrcnt <= cmdinfo_addr_4b_en ? 5'd 31 : 5'd 23;
    else if (addr_shift)  addrcnt <= addrcnt - 5'd 1;
  end

  always_comb begin
    address_d = address_q;
    if (addr_shift) begin
      address_d = {address_q[23:0], s2p_byte_i};
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      address_q <= '0;
    end else if (s2p_valid_i && addr_shift) begin
      address_q <= address_d;
    end
  end


  // payloadptr manage: spid_fifo2sram_adapter's fifoptr (wdepth) is reset by
  // CSb everytime. the written payload size should be visible to SW even CSb
  // is de-asserted.
  //
  // The logic observes payload_wvalid && payload_wready and increments the
  // payload pointer reset by sys_rst_ni not by rst_ni.
  logic payloadptr_inc, payloadptr_clr;
  logic [PayloadPtrW-1:0] payloadptr;
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni)      payloadptr <= '0;
    else if (payloadptr_clr) payloadptr <= '0;
    else if ((payloadptr != PayloadPtrW'(PayloadByte)) && payloadptr_inc) begin
      payloadptr <= payloadptr + PayloadPtrW'(1);
    end
  end

  // Synchronize to the sys_clk when CSb deasserted
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) sys_payload_depth_o <= '0;
    else if (sys_csb_deasserted_pulse_i) sys_payload_depth_o <= payloadptr;
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st_q <= StIdle;
    end else begin
      st_q <= st_d;
    end
  end


  // State Machine runs in SCK domain
  always_comb begin
    st_d = st_q;

    cmdfifo_wvalid  = 1'b 0;
    addrfifo_wvalid = 1'b 0;
    payload_wvalid  = 1'b 0;

    addr_update = 1'b 0;
    addr_shift  = 1'b 0;

    set_busy_o = 1'b 0;

    payloadptr_clr = 1'b 0;
    payloadptr_inc = 1'b 0;

    unique case (st_q)
      StIdle: begin
        if (s2p_valid_i && sel_dp_i == DpUpload) begin
          if (cmdinfo_addr_en) begin
            st_d = StAddress;

            // Address process (determines 32bit or 24bit)
            addr_update = 1'b 1;
          end else begin
            st_d = StPayload;
          end

          // Upload to SRAM right away.
          cmdfifo_wvalid = 1'b 1;

          // Assume cmdfifo_wready is 1 always (need to add assumption)

          if (cmd_info_i.busy) begin
            // Set BUSY
            set_busy_o = 1'b 1;
          end

          // Clear payload counter
          payloadptr_clr = 1'b 1;

        end
      end

      StAddress: begin
        addr_shift = 1'b 1;

        if (addrcnt == '0) begin
          st_d = StPayload;
        end
      end

      StPayload: begin
        // TERMINAL_STATE
        if (s2p_valid_i) begin
          payload_wvalid = 1'b 1;
          payloadptr_inc = 1'b 1;
        end

        // ASSUME payload_wready == 1'b1
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  //////////////
  // Instance //
  //////////////

  // TODO: Merge two FIFOs into one.
  // Design a module that has one SRAM Read port / one SRAM write port
  // and compile-time configurable # of FIFO ports + N of SramBase Address
  // (Preferrably variable width)

  // FIFO reset:
  // To maintain the pointer on read/ write side same, the FIFO uses
  // sys_rst_ni rather than rst_ni for the write port. The pointer is
  // maintained throughout the SPI transactions (CSb assertion/ de-assertion).
  //
  // As sys_rst_ni is not synchronized to the external clock, the sys_rst_ni
  // should be de-asserted when SPI line is in idle (CSb == 1).

  // CmdFifo
  prim_fifo_async_sram_adapter #(
    .Width        (CmdFifoWidth),
    .Depth        (CmdFifoDepth),
    .SramAw       (SramAw),
    .SramDw       (SramDw),
    .SramBaseAddr (CmdFifoBaseAddr)
  ) u_cmdfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (sys_rst_ni),
    .wvalid_i  (cmdfifo_wvalid),
    .wready_o  (cmdfifo_wready),
    .wdata_i   (cmdfifo_wdata ),
    .wdepth_o  (),

    .clk_rd_i  (sys_clk_i),
    .rst_rd_ni (sys_rst_ni),
    .rvalid_o  (sys_cmdfifo_rvalid_o),
    .rready_i  (sys_cmdfifo_rready_i),
    .rdata_o   (sys_cmdfifo_rdata_o),
    .rdepth_o  (sys_cmdfifo_depth_o),

    .r_full_o     (sys_cmdfifo_full_o),
    .r_notempty_o (sys_cmdfifo_notempty_o),

    .w_full_o (),

    .w_sram_req_o    (sck_sram_req    [SramCmdFifo]),
    .w_sram_gnt_i    (sck_sram_gnt    [SramCmdFifo]),
    .w_sram_write_o  (sck_sram_write  [SramCmdFifo]),
    .w_sram_addr_o   (sck_sram_addr   [SramCmdFifo]),
    .w_sram_wdata_o  (sck_sram_wdata  [SramCmdFifo]),
    .w_sram_wmask_o  (sck_sram_wmask  [SramCmdFifo]),
    .w_sram_rvalid_i (sck_sram_rvalid [SramCmdFifo]),
    .w_sram_rdata_i  (sck_sram_rdata  [SramCmdFifo]),
    .w_sram_rerror_i (sck_sram_rerror [SramCmdFifo]),

    .r_sram_req_o    (sys_sram_req    [SramCmdFifo]),
    .r_sram_gnt_i    (sys_sram_gnt    [SramCmdFifo]),
    .r_sram_write_o  (sys_sram_write  [SramCmdFifo]),
    .r_sram_addr_o   (sys_sram_addr   [SramCmdFifo]),
    .r_sram_wdata_o  (sys_sram_wdata  [SramCmdFifo]),
    .r_sram_wmask_o  (sys_sram_wmask  [SramCmdFifo]),
    .r_sram_rvalid_i (sys_sram_rvalid [SramCmdFifo]),
    .r_sram_rdata_i  (sys_sram_rdata  [SramCmdFifo]),
    .r_sram_rerror_i (sys_sram_rerror [SramCmdFifo])
  );

  // Connect to sys_cmdfifo_sram_o/_i
  assign sys_cmdfifo_sram_o = '{
    req:   sys_sram_req   [SramCmdFifo],
    we:    sys_sram_write [SramCmdFifo],
    addr:  sys_sram_addr  [SramCmdFifo],
    wdata: sys_sram_wdata [SramCmdFifo],
    wstrb: sram_mask2strb(sys_sram_wmask [SramCmdFifo])
  };
  assign sys_sram_rvalid [SramCmdFifo] = sys_cmdfifo_sram_i.rvalid;
  assign sys_sram_rdata  [SramCmdFifo] = sys_cmdfifo_sram_i.rdata ;
  assign sys_sram_rerror [SramCmdFifo] = sys_cmdfifo_sram_i.rerror;
  assign sys_sram_gnt    [SramCmdFifo] = sys_sram_req[SramCmdFifo];

  // AddrFifo
  prim_fifo_async_sram_adapter #(
    .Width        (AddrFifoWidth),
    .Depth        (AddrFifoDepth),
    .SramAw       (SramAw),
    .SramDw       (SramDw),
    .SramBaseAddr (AddrFifoBaseAddr)
  ) u_addrfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (sys_rst_ni),
    .wvalid_i  (addrfifo_wvalid),
    .wready_o  (addrfifo_wready),
    .wdata_i   (addrfifo_wdata ),
    .wdepth_o  (),

    .clk_rd_i  (sys_clk_i),
    .rst_rd_ni (sys_rst_ni),
    .rvalid_o  (sys_addrfifo_rvalid_o),
    .rready_i  (sys_addrfifo_rready_i),
    .rdata_o   (sys_addrfifo_rdata_o),
    .rdepth_o  (sys_addrfifo_depth_o),

    .r_full_o     (sys_addrfifo_full_o),
    .r_notempty_o (sys_addrfifo_notempty_o),

    .w_full_o (),

    .w_sram_req_o    (sck_sram_req    [SramAddrFifo]),
    .w_sram_gnt_i    (sck_sram_gnt    [SramAddrFifo]),
    .w_sram_write_o  (sck_sram_write  [SramAddrFifo]),
    .w_sram_addr_o   (sck_sram_addr   [SramAddrFifo]),
    .w_sram_wdata_o  (sck_sram_wdata  [SramAddrFifo]),
    .w_sram_wmask_o  (sck_sram_wmask  [SramAddrFifo]),
    .w_sram_rvalid_i (sck_sram_rvalid [SramAddrFifo]),
    .w_sram_rdata_i  (sck_sram_rdata  [SramAddrFifo]),
    .w_sram_rerror_i (sck_sram_rerror [SramAddrFifo]),

    .r_sram_req_o    (sys_sram_req    [SramAddrFifo]),
    .r_sram_gnt_i    (sys_sram_gnt    [SramAddrFifo]),
    .r_sram_write_o  (sys_sram_write  [SramAddrFifo]),
    .r_sram_addr_o   (sys_sram_addr   [SramAddrFifo]),
    .r_sram_wdata_o  (sys_sram_wdata  [SramAddrFifo]),
    .r_sram_wmask_o  (sys_sram_wmask  [SramAddrFifo]),
    .r_sram_rvalid_i (sys_sram_rvalid [SramAddrFifo]),
    .r_sram_rdata_i  (sys_sram_rdata  [SramAddrFifo]),
    .r_sram_rerror_i (sys_sram_rerror [SramAddrFifo])
  );
  // Connect to sys_addrfifo_sram_o/_i
  assign sys_addrfifo_sram_o = '{
    req:   sys_sram_req   [SramAddrFifo],
    we:    sys_sram_write [SramAddrFifo],
    addr:  sys_sram_addr  [SramAddrFifo],
    wdata: sys_sram_wdata [SramAddrFifo],
    wstrb: sram_mask2strb(sys_sram_wmask [SramAddrFifo])
  };
  assign sys_sram_rvalid [SramAddrFifo] = sys_addrfifo_sram_i.rvalid;
  assign sys_sram_rdata  [SramAddrFifo] = sys_addrfifo_sram_i.rdata ;
  assign sys_sram_rerror [SramAddrFifo] = sys_addrfifo_sram_i.rerror;
  assign sys_sram_gnt    [SramAddrFifo] = sys_sram_req[SramAddrFifo];

  // Payload Buffer
  spid_fifo2sram_adapter #(
    .FifoWidth (SpiByte),
    .FifoDepth (PayloadByte),

    .SramAw       (SramAw),
    .SramDw       (SramDw),
    .SramBaseAddr (PayloadBaseAddr),

    // CFG
    .EnPack (1'b1)
  ) u_payload_buffer (
    .clk_i,
    .rst_ni,

    .wvalid_i (payload_wvalid),
    .wready_o (payload_wready),
    .wdata_i  (payload_wdata ),

    // Does not use wdepth from the buffer as it is reset by CSb.
    .wdepth_o (),

    .sram_req_o    (sck_sram_req    [SramPayload]),
    .sram_gnt_i    (sck_sram_gnt    [SramPayload]),
    .sram_write_o  (sck_sram_write  [SramPayload]),
    .sram_addr_o   (sck_sram_addr   [SramPayload]),
    .sram_wdata_o  (sck_sram_wdata  [SramPayload]),
    .sram_wmask_o  (sck_sram_wmask  [SramPayload]),
    .sram_rvalid_i (sck_sram_rvalid [SramPayload]),
    .sram_rdata_i  (sck_sram_rdata  [SramPayload]),
    .sram_rerror_i (sck_sram_rerror [SramPayload])
  );

  // SramArbiter
  logic [SramDw-1:0] sram_wmask;
  prim_sram_arbiter #(
    .N      (NumSramIntf),
    .SramDw (SramDw),
    .SramAw (SramAw)
  ) u_arbiter (
    .clk_i,
    .rst_ni,

    .req_i       (sck_sram_req),
    .req_addr_i  (sck_sram_addr),
    .req_write_i (sck_sram_write),
    .req_wdata_i (sck_sram_wdata),
    .req_wmask_i (sck_sram_wmask),
    .gnt_o       (sck_sram_gnt),

    .rsp_rvalid_o (sck_sram_rvalid), // not used
    .rsp_rdata_o  (sck_sram_rdata), // not used
    .rsp_error_o  (sck_sram_rerror),

    .sram_req_o    (sck_sram_o.req),
    .sram_addr_o   (sck_sram_o.addr),
    .sram_write_o  (sck_sram_o.we),
    .sram_wdata_o  (sck_sram_o.wdata),
    .sram_wmask_o  (sram_wmask),
    .sram_rvalid_i (sck_sram_i.rvalid),
    .sram_rdata_i  (sck_sram_i.rdata),
    .sram_rerror_i (sck_sram_i.rerror)
  );
  assign sck_sram_o.wstrb = sram_mask2strb(sram_wmask);

  ///////////////
  // Assertion //
  ///////////////

  // As SCK fifo control can't handle the full condition. Assume the wready
  `ASSUME(CmdFifoNeverFull_M,  cmdfifo_wvalid  |-> cmdfifo_wready)
  `ASSUME(AddrFifoNeverFull_M, addrfifo_wvalid |-> addrfifo_wready)
  `ASSUME(PayloadNeverFull_M,  payload_wvalid  |-> payload_wready)

  // Assert FIFO wvalid onehot0
  `ASSERT(FifosOnlyOneValid_A,
    $onehot0({cmdfifo_wvalid, addrfifo_wvalid, payload_wvalid}))

  // Sram Arbiter does not have a push back mechanism. Assume grant is always 1

endmodule : spid_upload
