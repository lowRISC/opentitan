// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash Read Commands Processing block
//
// This module processes read commands and Mailbox address region.
//
/*
  Details:

  # Process

  Command Parser sends a command in the 8th bit. The datapath is selected at
  the same cycle.

  Read command process block uses the cmd_info data and determine how the
  module should operate. The cmd_info has enough information the module to
  operate such as the address mode (4B affected or not), the existence of the
  dummy cycles, the number of dummy cycles, the number of output lanes the
  command uses, and the number of address lines. Please refer
  spi_device_pkg::cmd_info_t for the details of the data structure.

  ## Address handling

  ### Address for Output commands

  As address comes through IO0 only, the state machine shifts the address
  one-by-one and decrement the address counter register by 1.

  When it reaches to the 4B address (addr[2]), it triggers DPSRAM state machine
  to fetch data from DPSRAM. And when it receives addr[0], at posedge the state
  machine moves to appropriate command state.

  ### Address for I/O commands

  Address comes through IO0,1 for the  dual I/O command, or IO0:3 for the quad
  I/O command.  The logic latches 2 or 4bit at a time. When it reaches valid
  4B address, it triggers the Dual-Port SRAM(DPSRAM) state machine to fetch
  data from the DPSRAM. Then, it moves to M byte state. The value is not used
  in current design.

  ### Mailbox when the mode is enabled

  If the address falls into mailbox address range while stacking address into
  a register, the state turns on mailbox selection bit. Then all out-going
  requests to DPSRAM for read point to the Mailbox section not to the Read
  Buffer section.

  ## Normal command

  Normal command sends the read data right after the address phase. Right
  after moved to the Normal command state, the state machine pushes proper
  byte into synchronous FIFO. The FIFO has the pass parameter enabled to get
  the data within a cycle.

  ## Fast Read command

  Moving into Fast Read command state is identical to the Normal read command
  state. The address state sends read request when it reaches 4B granularity.
  Then when the state moves to this Fast Read command state, the machine waits
  preconfigured dummy cycle. The default dummy cycle is 8. Then it follows same
  step as Normal read command state.

  ## Dual/ Quad Output command

  The state is similar to the Fast Read command. The dummy cycle for Dual/ Quad
  are 4 and 2 by default. But they can be configured by the software. The states
  send DPSRAM read request at every 2nd cycle in a byte for Dual command, 1st
  cycle in a byte (two beats) for Quad command.

  ## Dual/ Quad I/O command

  I/O commands have M byte prior to the dummy cycles. Read command module does
  not support continuous read feature that is described in M byte. So, Dual &
  Quad I/O commands state waits M byte then moves to Dual/ Quad output command
  states.

  ## Read SFDP command

  If the incoming datapath is not DpReadCmd but DpSfdp, then the request to
  the DPSRAM goes to the SFDP data section. The `cmd_info` should have the
  expected config for the SFDP command (e.g: 4B affected disabled,
  non-existence of the dummy cycle).

*/

`include "prim_assert.sv"

module spi_readcmd
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
  input clk_i,
  input rst_ni,

  input clk_out_i, // Output clock (inverted SPI_CLK)

  input sys_rst_ni, // System reset for buffer tracking pointers

  // From Command Parser
  // DpReadCmd activates readcmd module, and it sees opcode to determine its
  // mode inside (Normal/ Fast/ Dual/ Quad/ DualIO/ QuadIO)
  input sel_datapath_e sel_dp_i,

  // SRAM access
  output sram_l2m_t  sram_l2m_o,
  input  sram_m2l_t  sram_m2l_i,

  // Interface: SPI to Parallel
  input               s2p_valid_i,
  input spi_byte_t    s2p_byte_i,

  // Interface: Parallel to SPI
  // Should be latched to clk_out_i
  output logic      p2s_valid_o,
  output spi_byte_t p2s_byte_o,
  input  logic      p2s_sent_i,

  // Configurations:
  //    All configs come from peripheral clock domain.
  //    No CDC exists in between.
  input spi_mode_e spi_mode_i,

  input cmd_info_t              cmd_info_i,
  input logic [CmdInfoIdxW-1:0] cmd_info_idx_i,

  // Double buffering in bytes
  input [SramBufferAw-1:0] readbuf_threshold_i,

  // The command mode is 4B mode. Every read command receives 4B address
  input addr_4b_en_i,

  // Features
  input mailbox_en_i,
  input cfg_intercept_en_mbx_i, // Intercept

  // Mailbox Address base address
  // Only allow compile-time fixed size (1kB by default)
  input [31:0] mailbox_addr_i,
  //input [31:0] mailbox_mask_i,

  // Indicator to take SPI line in Passthrough mode
  output logic mailbox_assumed_o,

  // Read buf addr in SCK domain. It is synchronized to bus clock in the top
  // module
  output logic [31:0] readbuf_address_o,

  output io_mode_e io_mode_o,

  // Read watermark event occurs when current address exceeds the threshold cfg
  // value for the first time after hit the current read buffer (1kB
  // granularity).
  //
  // These signals are pulse signals.
  output logic sck_read_watermark_o,
  output logic sck_read_flip_o

);

  logic unused_p2s_sent ;
  assign unused_p2s_sent = p2s_sent_i;

  sram_err_t unused_sram_rerr;
  assign unused_sram_rerr = sram_m2l_i.rerror;

  logic unused_cmd_info_idx;
  assign unused_cmd_info_idx = ^cmd_info_idx_i;

  logic unused_cmd_info_members;
  assign unused_cmd_info_members = ^{
    cmd_info_i.valid,           // cmdparse checks the valid bit
    cmd_info_i.addr_swap_en,    // address swap feature is used in Passthrough
    cmd_info_i.opcode,          // Does not need to check opcode. (fixed slot)
    cmd_info_i.payload_dir,     // Always output mode
    cmd_info_i.payload_swap_en, // Used in passthrough mode only
    cmd_info_i.upload,
    cmd_info_i.busy
    };

  `ASSERT(ValidCmdConfig_A,
          main_st == MainAddress |-> (cmd_info_i.addr_mode != AddrDisabled)
          && cmd_info_i.payload_dir == PayloadOut
          && cmd_info_i.valid)

  /////////////////
  // Definitions //
  /////////////////

  // The expected FSM sequence for each command:
  //
  //  - Read Data: Reset -> Address -> Output
  //  - Fast Read (Single/ Dual/ Quad): Reset -> Address -> Dummy -> Output
  //  - Fast Read Dual IO/ Quad IO: Reset -> Address -> MByte -> Dummy -> Output
  //  - Read SFDP: Reset -> Address -> Output
  typedef enum logic [3:0] {
    // Reset: Wait until the datapath for Read command is activated by cmdparse
    // The cmd_info is valid after the 8th posedge of SCK.
    MainReset,

    // Address
    //
    //   In this state, the FSM stacks incoming byte from s2p up to 3B or 4B
    //   based on the config by SW. When FSM moves from Reset to this state,
    //   it sets the IO mode to Single/ Dual/ Quad depending on the incoming
    //   SPI command.
    //
    //   In this state, when it stacks addr[2] bit, which is 3rd from last in
    //   Single IO, 2nd from the last in Dual IO, and the last in Quad IO, it
    //   triggers Fetch State Machine to fetch data from Dual Port SRAM in
    //   SPI_DEVICE.
    //
    //   For I/O commands, the state moves to MByte state.
    //   For Fast commands, the state moves to Dummy state.
    //   For Normal Read command, the state moves to Output state directly.
    MainAddress,

    // MByte
    //
    //   IO commands (Dual I/O, Quad I/O) has M byte following Address. It is
    //   normally used for "continuous read" operation. This logic does not
    //   support the feature, so ignoring it then moves to Dummy state.
    MainMByte,

    // Dummy: Wait until it reaches dummy cycles, then moves to Output state
    MainDummy,

    // Output
    //
    //   After passing the dummy cycle or skipping it for Normal Read command,
    //   The state drives SPI interface to send data. This state always assumes
    //   the data is ready in the sync fifo (see instance below). The Fetch
    //   Machine always prepares the data in advance up to designated level.
    //   The prefetch does not affect the watermark that SW has configured. The
    //   event occurs only when the byte is indeed sent through SPI lines.
    //
    //   This state machine watches the sent address and raises an event if it
    //   exceeds the level. This feature is not turned on for Mailbox address.
    MainOutput,

    // Error: Wait until CSb deasserted
    MainError
  } main_st_e;
  main_st_e main_st, main_st_d;

  /////////////
  // Signals //
  /////////////

  // Address mode in cmd_info
  addr_mode_e cmdinfo_addr_mode;

  // Address shift & latch
  logic addr_ready_in_word, addr_ready_in_halfword;
  logic addr_latched;
  logic addr_shift_en;
  logic addr_latch_en;
  logic addr_inc; // increase address by 1 byte. Used to track the current addr
  // Address size is latched when the state machine moves to the MainAddress
  // state based on the cmd_info.addr_mode and addr_4b_en_i
  logic [4:0] addr_cnt_d, addr_cnt_q;
  logic addr_cnt_set; // no need to clear the counter
  logic addr_latched_d;

  logic [31:0] addr_q, addr_d;

  // Read buffer access address.
  //
  // This differs from addr_q. addr_q is to maintain the SRAM access.
  // readbuf_addr is to track the Read command address which does not fall
  // into SFDP, Mailbox.
  logic [31:0] readbuf_addr;
  // Read Buffer update: addr_latch_en at the last addr beat & addr_inc
  logic readbuf_update;
  // When FSM is about to move to Output state, FSM triggers readbuf to operate.
  logic readbuf_start;


  // Dummy counter
  logic dummycnt_eq_zero;
  logic load_dummycnt;
  logic [2:0] dummycnt;

  // IO Mode selection

  // SRAM signals
  // Compare addr_d[SramAw-1:2] and mailbox_addr_i with mailbox_mask_i. If the
  // value falls into mailbox, set this.  Even this is set, it only uses when
  // sram address is sent.
  logic addr_d_in_mailbox, addr_q_in_mailbox;

  logic [31:0] mailbox_masked_addr_d, mailbox_masked_addr_q;

  // Double buffering signals
  logic readbuf_idx; // 0 or 1
  logic readbuf_flip; // if this is asserted, readbuf_idx flips.

  // bit count within a word
  logic bitcnt_update;
  logic bitcnt_dec;
  logic [2:0] bitcnt; // count down from 7 or partial for first unaligned

  // FIFO
  logic unused_fifo_rvalid, fifo_pop;
  spi_byte_t fifo_rdata;

  logic [7:0] p2s_byte;
  logic       p2s_valid_inclk;

  logic sfdp_hit;
  assign sfdp_hit = sel_dp_i == DpReadSFDP;

  // Events: watermark, flip
  logic read_watermark, read_flip;

  // SPI Mode
  logic  spid_in_flashmode;
  assign spid_in_flashmode = (spi_mode_i == FlashMode);

  //////////////
  // Datapath //
  //////////////

  // Address Shifting.
  // the data comes from S2P module, which sends valid signal with spi_byte_t.
  // So, if the logic sees `valid` only, it can't latch the exact word address.
  // This logic latches in byte based until the 2nd last byte. Then merging
  // the incoming byte (premature) to organize 4B address.

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q <= '0;
    end else if (addr_latch_en) begin
      addr_q <= addr_d;
    end
  end

  // readbuf_addr is visible to SW after CSb is de-asserted. (last_read_addr)
  //
  // It indicates the last byte address the host read.
  // To precisely represent the last byte:
  //
  // - the logic does not latch address field (not yet read the byte)
  // - the logic latches `addr_q` at the last beat. But compare `addr_q` to
  //   mailbox address.
  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      readbuf_addr <= '0;
    end else if ((main_st == MainOutput) && (sel_dp_i == DpReadCmd)
      && addr_latch_en && !(mailbox_en_i && addr_q_in_mailbox)
      && spid_in_flashmode) begin
      readbuf_addr <= addr_q;
    end
  end

  assign readbuf_address_o = readbuf_addr;

  always_comb begin
    addr_d = addr_q; // default value. In 3B mode, upper most byte is 0
    addr_latch_en = 1'b0;

    // TODO: Handle the case of IO command
    if (addr_ready_in_word) begin
      // Return word based address, but should not latch
      addr_d = {addr_q[23:0], s2p_byte_i[5:0], 2'b00};
    end else if (addr_ready_in_halfword) begin
      // When addr is a cycle earlier than full addr, sram req sent in
      // spid_readsram
      addr_d = {addr_q[23:0], s2p_byte_i[6:0], 1'b 0};
    end else if (addr_shift_en && s2p_valid_i) begin
      // Latch
      addr_d = {addr_q[23:0], s2p_byte_i[7:0]};
      addr_latch_en = 1'b 1;
    end else if (addr_inc) begin
      // Increase the address to next
      addr_d = addr_q[31:0] + 1'b1;
      addr_latch_en = 1'b 1;
    end
  end

  // BEGIN: Address Count =====================================================
  // addr_cnt is to track the current shifted bit position in the address field
  assign addr_ready_in_word     = (addr_cnt_d == 5'd 2);
  assign addr_ready_in_halfword = (addr_cnt_d == 5'd 1);

  // addr_latched should be a pulse to be used in spid_readsram
  assign addr_latched_d = (addr_cnt_d == 5'd 0);

  prim_edge_detector #(
    .Width      (1),
    .ResetValue (1'b 0),
    .EnSync     (1'b 0)
  ) u_addr_latch_pulse (
    .clk_i,
    .rst_ni,

    .d_i               (addr_latched_d),
    .q_sync_o          (              ),
    .q_posedge_pulse_o (addr_latched  ),
    .q_negedge_pulse_o (              )
  );

  assign cmdinfo_addr_mode = get_addr_mode(cmd_info_i, addr_4b_en_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q <= '0;
    end else begin
      addr_cnt_q <= addr_cnt_d;
    end
  end

  always_comb begin : addr_cnt
    addr_cnt_d = addr_cnt_q;
    if (addr_cnt_set) begin
      // Set to the addr size based on cmd_info_i
      // If addr_mode && addr_4b_en is Addr4B, then 32, if not, 24
      // addr_cnt_d starts from the max -1. As addr_cnt_set is asserted when
      // FSM moves from Reset to Address. At that time of the transition, the
      // datapath should latch the Address[31] or Address[23] too. So, it
      // already counts one beat.
      addr_cnt_d = (cmdinfo_addr_mode == Addr4B) ? 5'd 31 : 5'd 23;

      // TODO: Dual IO/ Quad IO case
    end else if (addr_cnt_q == '0) begin
      addr_cnt_d = addr_cnt_q;
    end else if (addr_shift_en) begin
      // Stacking the address, decrease the address counter
      addr_cnt_d = addr_cnt_q - 1'b 1;
    end
  end
  // END:   Address Count -----------------------------------------------------

  // Dummy Counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dummycnt <= '0;
    end else if (load_dummycnt) begin
      // load quad_io
      dummycnt <= cmd_info_i.dummy_size;
    end else if (!dummycnt_eq_zero) begin
      dummycnt <= dummycnt - 1'b 1;
    end
  end
  assign dummycnt_eq_zero = ~|dummycnt;

  // FIFO bit count
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bitcnt <= '0;
    end else if (bitcnt_update) begin
      unique case (cmd_info_i.payload_en)
        4'b 0010: bitcnt <= 3'h 7;
        4'b 0011: bitcnt <= 3'h 6;
        4'b 1111: bitcnt <= 3'h 4;
        default:  bitcnt <= 3'h 7;
      endcase
    end else if (bitcnt_dec) begin
      unique case (cmd_info_i.payload_en)
        4'b 0010: bitcnt <= bitcnt - 3'h 1;
        4'b 0011: bitcnt <= bitcnt - 3'h 2;
        4'b 1111: bitcnt <= bitcnt - 3'h 4;
        default:  bitcnt <= bitcnt - 3'h 1;
      endcase
    end
  end

  //= BEGIN: SRAM Datapath ====================================================
  // Main FSM trigger this datapath. This logic calculates the correct address

  // Address conversion
  // Convert into masked address
  localparam int unsigned MailboxAw = $clog2(MailboxDepth);
  localparam logic [31:0] MailboxMask = {{30-MailboxAw{1'b1}}, {2+MailboxAw{1'b0}}};

  assign mailbox_masked_addr_d = addr_d & MailboxMask;
  assign mailbox_masked_addr_q = addr_q & MailboxMask;

  // Only valid when logic sends SRAM request
  assign addr_d_in_mailbox = (mailbox_masked_addr_d == mailbox_addr_i);
  assign addr_q_in_mailbox = (mailbox_masked_addr_q == mailbox_addr_i);

  // internal addr is the address that the logic tracks.
  // the first address comes from host system and then the internal logic
  // manages the address to follow.

  logic sram_req;

  // Check if mailbox and intercept config, then raises mailbox_assumed.
  // The signal shall be registered in SCK in.
  // Then, spi_device top will latch to SCK out
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) mailbox_assumed_o <= 1'b 0;
    else if (sram_req && mailbox_en_i && cfg_intercept_en_mbx_i
            && addr_d_in_mailbox) begin
      mailbox_assumed_o <= 1'b 1;
    end else if (mailbox_en_i && cfg_intercept_en_mbx_i
                && addr_d_in_mailbox && (bitcnt == 3'h 0)) begin
      // Keep checking if the next byte falls into the mailbox region
      mailbox_assumed_o <= 1'b 1;
    end else if (!addr_d_in_mailbox && (bitcnt == 3'h 0)) begin
      // At every byte, Check the address goes out of mailbox region.
      mailbox_assumed_o <= 1'b 0;
    end
  end
  //- END:   SRAM Datapath ----------------------------------------------------

  //= BEGIN: FIFO to P2S datapath =============================================
  assign p2s_byte = fifo_rdata;

  // outclk latch
  // can't put async fifo. DC constraint should have half clk datapath
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) begin
      p2s_valid_o <= 1'b 0;
      p2s_byte_o  <= '0 ;
    end else begin
      p2s_valid_o <= p2s_valid_inclk;
      p2s_byte_o  <= p2s_byte;
    end
  end
  //- END:   FIFO to P2S datapath ---------------------------------------------

  //= BEGIN: Double Buffering =================================================

  // Readbuf Index:
  //
  // this signal is not reset by CSb. The value should be alive throughout the
  // CSb event. (last_access_addr too)

  always_ff @(posedge clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      readbuf_idx <= 1'b 0;
    end else if (readbuf_flip) begin
      // readbuf_flip happens when the module completes the second to the last
      // byte of a buffer through SPI. There will be a chance that will be
      // cancelled by de-asserting CSb. This logic does not guarantee to cover
      // that corner case. It expects to complete a byte transfer if it sends
      // the first beat of the byte.
      readbuf_idx <= ~readbuf_idx;
    end
  end

  // readbuf_flip
  // TODO: implement. Below is temporary.
  assign readbuf_flip = (main_st == MainOutput && addr_q[9:0] == '1);

  //- END:   Double Buffering -------------------------------------------------

  ///////////////////
  // State Machine //
  ///////////////////

  //= BEGIN: Main state machine ===============================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      main_st <= MainReset;
    end else begin
      main_st <= main_st_d;
    end
  end

  always_comb begin
    main_st_d = main_st;

    load_dummycnt = 1'b 0;

    // address control
    addr_cnt_set = 1'b 0;
    addr_inc = 1'b 0;
    sram_req = 1'b 0;
    addr_shift_en = 1'b 0;

    p2s_valid_inclk = 1'b 0;
    fifo_pop        = 1'b 0;

    bitcnt_update = 1'b 0;
    bitcnt_dec = 1'b 0;

    io_mode_o = SingleIO;

    readbuf_start  = 1'b 0;
    readbuf_update = 1'b 0;

    unique case (main_st)
      MainReset: begin
        if (sel_dp_i inside {DpReadCmd, DpReadSFDP}) begin
          // Any readcommand goes to MainAddress state to latch address
          // 3B, 4B handles inside address
          main_st_d = MainAddress;

          addr_cnt_set = 1'b 1;
        end
      end

      MainAddress: begin
        addr_shift_en = 1'b 1;

        // TODO: DualIO/ QuadIO case
        if (addr_ready_in_word) begin
          sram_req = 1'b 1;
        end

        if (addr_latched) begin
          // update bitcnt. If input address is not word aligned, bitcnt
          // could be 23, 15, or 7
          bitcnt_update = 1'b 1;

          // Next state:
          //  MByte if mbyte enabled
          //  Dummy if mbyte = 0 and dummy_en = 1
          //  Output if mbyte = 0 and dummy_en = 0
          unique casez ({cmd_info_i.mbyte_en, cmd_info_i.dummy_en})
            2'b 00: begin
              // Moves to Output directly
              main_st_d = MainOutput;
              readbuf_start  = 1'b 1;
              readbuf_update = 1'b 1;
            end

            2'b 01: begin
              // Dummy Enabled
              main_st_d = MainDummy;

              load_dummycnt = 1'b 1;
            end

            2'b 1?: begin
              // Regardless of Dummy
              main_st_d = MainMByte;

              // TODO: Set MByte latency (3 or 1)
            end

            default: begin
              main_st_d = MainError;
            end
          endcase
        end
      end

      MainMByte: begin
        if (s2p_valid_i) begin
          main_st_d = MainDummy;

          load_dummycnt = 1'b 1;
        end
      end

      MainDummy: begin
        if (dummycnt_eq_zero) begin
          main_st_d = MainOutput;
          readbuf_start  = 1'b 1;
          readbuf_update = 1'b 1;
        end
      end

      MainOutput: begin
        bitcnt_dec = 1'b 1;

        // Note: p2s accepts the byte and latch inside at the first beat.
        // So, it is safe to change the data at the next cycle.
        p2s_valid_inclk = 1'b 1;

        // DeadEnd until CSb deasserted
        // Change Mode based on the payload_en[3:0]
        // Return data from FIFO
        unique case (cmd_info_i.payload_en)
          4'b 0010: io_mode_o = SingleIO;
          4'b 0011: io_mode_o = DualIO;
          4'b 1111: io_mode_o = QuadIO;
          default:  io_mode_o = SingleIO;
        endcase

        if (bitcnt == 3'h 0) begin
          // Increase addr by 1 byte
          addr_inc = 1'b 1;

          // When address is begin updated, ask readbuf to update the state too
          readbuf_update = 1'b 1;

          // sent all words
          bitcnt_update = 1'b 1;
          // TODO: FIFO pop here?
          fifo_pop = 1'b 1;
        end
      end

      MainError: begin
        main_st_d = MainError;
      end

      default: begin
        main_st_d = MainReset;
      end
    endcase
  end
  //- END:   Main state machine -----------------------------------------------

  // Events: register
  // watermark, flip are pulse signals. watermark pulse width is 1 SCK.
  // flip pulse width varies inside readbuffer and changed into 1 SCK width.
  // They are not registered (output of comb logic).
  // As these signals goes into prim_pulse_sync, no need to register here.
  assign sck_read_watermark_o = read_watermark;
  assign sck_read_flip_o      = read_flip;

  ///////////////
  // Instances //
  ///////////////

  spid_readsram #(
    .ReadBaseAddr    (ReadBaseAddr),
    .ReadBufferDepth (ReadBufferDepth),
    .MailboxBaseAddr (MailboxBaseAddr),
    .MailboxDepth    (MailboxDepth),
    .SfdpBaseAddr    (SfdpBaseAddr),
    .SfdpDepth       (SfdpDepth)
  ) u_readsram (
    .clk_i,
    .rst_ni,

    .sram_read_req_i   (sram_req),
    .addr_latched_i    (addr_latched),
    .current_address_i (addr_d), // TODO: Change it

    .mailbox_en_i,
    .mailbox_addr_i,

    .sfdp_hit_i    (sel_dp_i == DpReadSFDP),

    .sram_l2m_o,
    .sram_m2l_i,

    // FIFO
    .fifo_rvalid_o (unused_fifo_rvalid),
    .fifo_rready_i (fifo_pop),
    .fifo_rdata_o  (fifo_rdata)
  );

  // Double Buffer Management logic
  spid_readbuffer u_readbuffer (
    .clk_i,
    .rst_ni,

    .sys_rst_ni,

    .spi_mode_i,

    .current_address_i (addr_d),
    .threshold_i       (readbuf_threshold_i),

    .sfdp_hit_i    (sfdp_hit),
    .mailbox_hit_i (addr_d_in_mailbox),
    .mailbox_en_i  (mailbox_en_i),

    .start_i (readbuf_start),

    .address_update_i (readbuf_update),

    .event_watermark_o (read_watermark),
    .event_flip_o      (read_flip)
  );

  ////////////////
  // Assertions //
  ////////////////

  // `addr_inc` should not be asserted in Address phase
  `ASSERT(AddrIncNotAssertInAddressState_A, addr_inc |-> main_st != MainAddress)

  // Assume mailbox addr config is mailbox size.
  // As depth is # of entries and the entry is word, the size should add 2bits
  `ASSUME(MailboxSizeMatch_M, mailbox_addr_i[$clog2(MailboxDepth)+1:0] == '0)


endmodule : spi_readcmd
