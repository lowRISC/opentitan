// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device Passthrough module.
//
/*
 * # Passthrough
 *
 * The OpenTitan SPI Device has a feature for snooping the SPI transactions from
 * a host system to a SPI flash device and for intervening against unauthorized
 * traffic. It is mainly intended for blocking any harmful read/ write requests
 * and for guaranteeing the return of genuine binary images to the host system.
 *
 * This module does two things:
 *
 * 1. It blocks any downstream commands if they are not permitted.
 * 2. It swaps the address field for read commands to support an A/B scheme.
 *
 * ## Command Filter
 *
 * The Command Filter blocks incoming commands if they are in the block list CSR
 * that SW has configured. When it blocks, it raises CSb (to high) at the 8th
 * SPI_CLK edge and holds SPI_CLK to low until the host system releases its CSb.
 *
 * The module uses a clock gating cell to not propagate the SPI_CLK to the
 * attached SPI Flash device, mainly in order to not introduce glitches on the
 * CSb line. If the module does not hold the SPI_CLK, then CSb needs one more
 * clock to remove the glitch. The timing delay means that this design will miss
 * the tming to raise CSb in order to cancel the self-complete commands such as
 * chip erase command.
 *
 * To make CSb de-assertion work, there are a few assumptions:
 *
 * 1. De-asserting CSb in the middle of transmit does not degrade the device
 *    quality.
 * 2. If CSb is de-asserted prior to the 8th SPI_CLK, the SPI flash device
 *    cancels the process without making any assumptions about the expected
 *    behavior. For example, the SPI flash device does not charge the
 *    charge-pump in the 7th beat to prepare the chip for erasure.
 *
 * Based on the information given, it is expected that the assumptions above are
 * satisfied.
 *
 * ## Address Manipulation
 *
 * SW can configure this module to swap the SPI line 0 to the downstream device
 * for the first 32 beats of data after the SPI command. Currently the only
 * supported commands are Read commands except for Dual IO and Quad IO commands.
 *
 * Due to the complexity of the design, this module does not support address
 * data for the IO commands, as the address field comes from two or four SPI
 * lines.
 *
 * SPI_DEVICE provides two programmable CSRs to support the address manipulation
 * feature. One is the mask register and another is actual data sending to the
 * downstream device.
 *
 * The mask register indicates the address bit to be swapped. If the mask bit
 * corresponding to the address bit position is 1, then the value transferred to
 * the downstream device is the value from the data register rather than the
 * value from the host system.
 *
 * Both registers are 32-bit registers. If 4B address mode is not enabled, only
 * lower 24-bit from the registers are used for the address manipulation.
 *
 * The usage of this feature may vary, but the main purpose is to provide an A/B
 * binary image. The Root-of-Trust device verifies the binary image sitting
 * inside the SPI flash device. If the image has been manipulated by malicious
 * attacks or reliability issues, then SW in RoT can redirect the host system's
 * requests to the other half partitions in the flash device.
 */
module spi_passthrough
  import spi_device_pkg::*;
(
  input clk_i,   // SPI input clk
  input rst_ni,  // SPI reset

  input clk_out_i, // SPI output clk

  // Configurations
  //
  // command filter information is given as 256bit register. It is subject to be
  // changed if command config is stored in DPSRAM. If that is supported, the
  // command config is valid at the 6th command cycle and given only 8 bits.
  input [255:0] cfg_cmd_filter_i,

  // address manipulation
  input [31:0] cfg_addr_mask_i,
  input [31:0] cfg_addr_value_i,

  // first byte of write payload manipulation
  input [31:0] cfg_payload_mask_i,
  input [31:0] cfg_payload_data_i,

  // Address mode
  input cfg_addr_4b_en_i,

  input spi_mode_e spi_mode_i,

  // Command Info structure
  input cmd_info_t [NumCmdInfo-1:0] cmd_info_i,

  // SPI in
  //
  // Though it would be best if passthrough is able to re-use existing spi_s2p
  // and cmdparse, but passthrough has to implement its own s2p and cmdparse to
  // support the A/B binary scheme.
  input              host_sck_i,
  input              host_csb_i,
  input        [3:0] host_s_i,
  output logic [3:0] host_s_o,    // clk_out_i domain
  output logic [3:0] host_s_en_o, // clk_out_i domain

  // SPI to SPI_HOST and terminal to the downstream device
  output passthrough_req_t passthrough_o,
  input  passthrough_rsp_t passthrough_i,

  // Mailbox indicator
  //
  // If a read command falls into the mailbox address and the mailbox feature is
  // enabled, the `Read Command` process module sends a signal to passthrough to
  // take the control of the SPI line. If this signal asserts during Address
  // phase, passthrough drops CSb to SPI Flash device and waits host's CSb
  // de-assertion.
  input mailbox_hit_i,

  // event
  // `cmd_filtered`: indicator of the incoming command filtered out
  output event_cmd_filtered_o
);

  /////////////////
  // Definitions //
  /////////////////

  // State
  typedef enum logic [2:0] {
    // In Idle state, it forwards the incoming SPI to SPI_HOST and eventually
    // to SPI Flash Device.
    StIdle,

    // When hitting the 8th beat (precisely 7 and half), the State machine
    // checks incoming data and determine if blocks the command or keep forward
    // to downstream device based on given config, cmd_filter.
    StFilter,

    // If a command filtered, the SCK to SPI_HOST Ip turned off and CSb
    // deasserted in StWait. The SCK shall be turned off in StFilter. In this
    // Wait state, the state machine waits for CSb de-assertion from the host
    // system.
    StWait,

    // Output command handling.
    //
    // This is mostly duplicated code from SPI Flash mode, but exists here to
    // control the output enable. In Passthrough mode, if the command is
    // allowed, the data comes from the downstream device, but it doesn't give
    // any hint of the output state (high-Z or driving).
    //
    // So, Passthrough module shall follow the SPI protocol to control `oe` of
    // upstream pads. It follows the same protocol as described in Read Command
    // module, Status Module, SFDP / JEDEC module.
    //
    // When St from StIdle or StAddress moves to StHighZ, it shall set wait
    // timer. The wait timer expires, StHighZ moves to StDriving, which is
    // dead-end until CSb de-asserted.
    StDriving,
    StHighZ,

    // Address manipulation
    //
    // One special feature of SPI Passthrough is A/B binary image support. The
    // logic can swap certain beats of data to pre-configured value. In this
    // state, the logic sees addr_mask and data and swaps the line if necessary.
    // After this, the ST moves to StDriving, or StHighZ.
    //
    // If the address hits the Mailbox region and the SW has enabled the
    // mailbox, then ST cancels current transaction and moves to StWait state.
    StAddress,

    // MByte
    StMByte
  } passthrough_st_e;
  passthrough_st_e st, st_d;

  /*
  localparam cmd_type_t CmdInfoNone = '{
    addr_en:          1'b 0,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 0,
    dummy_en:         1'b 0,
    payload_en:       4'h 0,
    payload_dir:  PayloadIn,
    addr_size:           '0,
    dummy_size:          '0
  };

  localparam cmd_type_t CmdInfoPayloadIn = '{
    addr_en:          1'b 0,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 0,
    dummy_en:         1'b 0,
    payload_en:       4'h 1,
    payload_dir:  PayloadIn,
    addr_size:           '0,
    dummy_size:          '0
  };

  localparam cmd_type_t CmdInfoPayloadOut = '{
    addr_en:          1'b 0,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 0,
    dummy_en:         1'b 0,
    payload_en:       4'h 2, // S[1]
    payload_dir: PayloadOut,
    addr_size:           '0,
    dummy_size:          '0
  };

  localparam cmd_type_t CmdInfoAddrPayloadIn = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 0,
    payload_en:       4'h 1, // S[0] only
    payload_dir:  PayloadIn, // Host sends Data
    addr_size:           '0, // Logic decide
    dummy_size:          '0
  };

  localparam cmd_type_t CmdInfoAddrPayloadInQuad = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 0,
    payload_en:       4'h F, // S[3:0]
    payload_dir:  PayloadIn, // Host sends Data
    addr_size:           '0, // Logic decide
    dummy_size:          '0
  };

  localparam cmd_type_t CmdInfoAddrPayloadOut = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 1,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 0,
    payload_en:       4'h 2, // S[1] only
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:          '0
  };

  // Address + Dummy + Payload but Address is 3B always
  localparam cmd_type_t CmdInfoAddr3BDummyPayloadOut = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 0,
    dummy_en:         1'b 1,
    payload_en:       4'h 2, // S[1] only
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:        'h 7
  };

  localparam cmd_type_t CmdInfoAddrDummyPayloadOut = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 1,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 1,
    payload_en:       4'h 2, // S[1] only
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:        'h 7
  };

  localparam cmd_type_t CmdInfoAddrDummyPayloadOutDual = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 1,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 1,
    payload_en:       4'h 3, // S[1:0] only
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:        'h 7
  };

  localparam cmd_type_t CmdInfoAddrDummyPayloadOutQuad = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 1,
    addr_4b_affected: 1'b 1,
    dummy_en:         1'b 1,
    payload_en:       4'h F, // S[3:0]
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:        'h 7
  };

  localparam cmd_type_t CmdInfoAddr = '{
    addr_en:          1'b 1,
    addr_swap_en:     1'b 0,
    addr_4b_affected: 1'b 0, // TODO: ??
    dummy_en:         1'b 0,
    payload_en:       4'h 0,
    payload_dir: PayloadOut, // Flash device sends Data
    addr_size:           '0, // Logic decide
    dummy_size:        'h 0
  };
  */

  /* Not synthesizable in DC
  localparam cmd_type_t PassThroughCmdInfoOld [256] = '{
    // 8'h 00
    'h 00: CmdInfoNone,

    // 8'h 01 Write Status 1
    'h 01: CmdInfoPayloadIn,
    // 8'h 15 Write Statur 2
    'h 31: CmdInfoPayloadIn,
    // 8'h 11 Write Status 3
    'h 11: CmdInfoPayloadIn,

    // 8'h 02 Page Program
    'h 02: CmdInfoAddrPayloadIn,
    // 8'h 32 Quad Input Page Program : Expect to be filtered
    'h 32: CmdInfoAddrPayloadInQuad,

    // 8'h 03 Read Data
    'h 03: CmdInfoAddrPayloadOut,

    // 8'h 04 Write Disable
    'h 04: CmdInfoNone,

    // 8'h 05 Read Status 1
    'h 05: CmdInfoPayloadOut,
    // 8'h 35 Read Status 2
    'h 35: CmdInfoPayloadOut,
    // 8'h 15 Read Status 3
    'h 15: CmdInfoPayloadOut,

    // 8'h 06 Write Enable
    'h 06: CmdInfoNone,

    // 8'h 0B Fast Read
    'h 0B: CmdInfoAddrDummyPayloadOut,
    // 8'h 3B Fast Read Dual Output
    'h 3B: CmdInfoAddrDummyPayloadOutDual,
    // 8'h 6B Fast Read Quad Output
    'h 6B: CmdInfoAddrDummyPayloadOutQuad,

    // 8'h 20 Sector Erase (4kB)
    'h 20: CmdInfoAddr,
    // 8'h 52 Block Erase (32kB)
    'h 52: CmdInfoAddr,
    // 8'h D8 Block Erase (64kB)
    'h D8: CmdInfoAddr,

    // 8'h 36 Individual Block Lock
    'h 36: CmdInfoAddr,
    // 8'h 39 Individual Block Unlock
    'h 39: CmdInfoAddr,
    // 8'h 3D Read Block Lock
    'h 3D: CmdInfoAddrPayloadOut,

    // 8'h 38 Enter QPI : Expect to be filtered
    'h 38: CmdInfoNone,

    // 8'h 42 Program Security Register
    // 8'h 44 Erase Security Register
    // 8'h 48 Read Security Register

    // 8'h 4B Read Unique ID

    // 8'h 5A Read SFDP
    'h 5A: CmdInfoAddr3BDummyPayloadOut,

    // 8'h 90 Manufacture/Device ID

    // 8'h 9F JEDEC ID
    'h 9F: CmdInfoPayloadOut,


    default: CmdInfoNone
  };
  */


  /////////////
  // Signals //
  /////////////

  // internal clock
  logic [3:0] host_s_en_inclk;
  logic [3:0] device_s_en_inclk;

  // Indicate Passthrough mode is enabled or not.
  logic is_active;
  assign is_active = (spi_mode_i == PassThrough);

  logic [7:0] opcode, opcode_d;

  logic unused_opcode_7;
  assign unused_opcode_7 = opcode[7];

  // If the filter becomes 1 on the 8th beat, it lowers SCK enable signal to CG
  // cell then, at the 8th posedge of SCK, csb_deassert becomes 1.
  //                      ____      ____      ____
  // SCK             ____/ 7  \____/ 8  \____/
  //                             ___
  // filter       _______/XXXXXX/   \______________
  //              ______________
  // sck_gate_en                \__________________
  //                                 ______________
  // csb_deassert __________________/
  logic filter;

  // If 1, SCK propagates to the downstream SPI Flash device.
  logic sck_gate_en;

  // CSb to the downstream device control If 1, CSb is de-asserted. This signal
  // is glitch sensitive. This value is changed at SCK posedge. This does not
  // drive CSb output directly. CSb to downstream is OR-ed with this and CSb
  // from host system.
  //
  // `cdb_deassert` should be latched at the posedge of SCK. `filter` signal is
  // computed in between the 7th posedge of SCK and the 8th posedge. As the
  // command bit does not arrive until the 7th negedge of SCK, the filter signal
  // is not valid in the first half of the period. By latching the filter signal
  // at the posedge of the SCK, csb_deassert always shows correct value if the
  // command needs to be filtered or not.
  //
  // However, the CSb output to the downstream flash device is better to be in
  // the out clock domain. It helps the design constraints to be simpler. So,
  // the `csb_deassert` is again latched at the outclk (which is the negedge of
  // SCK).
  logic csb_deassert;
  logic csb_deassert_outclk;

  // Temp port connection
  logic unused_payload_swap;
  assign unused_payload_swap = ^{cfg_payload_data_i, cfg_payload_mask_i};

  // == BEGIN: Counters  ======================================================
  // bitcnt to count up to dummy
  localparam int unsigned MetaMaxBeat = 8+32+8; // Cmd + Addr + Dummy
  localparam int unsigned MetaBitCntW = $clog2(MetaMaxBeat);
  logic [MetaBitCntW-1:0] bitcnt;

  // Address or anything host driving after opcode counter
  logic [AddrCntW-1:0] addrcnt, addrcnt_outclk;

  // Dummy counter
  logic [DummyCntW-1:0] dummycnt, dummycnt_d;
  // -- END:   Counters  ------------------------------------------------------

  // event
  assign event_cmd_filtered_o = filter;

  // Mailbox hit.
  logic mailbox_hit;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) mailbox_hit <= 1'b 0; // reset by CSb
    else if (mailbox_hit_i) mailbox_hit <= 1'b 1; // set by event
  end

  //////////////
  // Datapath //
  //////////////

  // Opcode Latch
  assign opcode_d = {opcode[6:0], host_s_i[0]};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      opcode <= 8'h 00;
    end else if (bitcnt < MetaBitCntW'(8)) begin
      opcode <= opcode_d;
    end
  end

  // Command Filter: CSb control
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)     csb_deassert <= 1'b 0;
    else if (filter) csb_deassert <= 1'b 1;
  end
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) csb_deassert_outclk <= 1'b 0;
    else         csb_deassert_outclk <= csb_deassert;
  end

  // Look at the waveform above to see why sck_gate_en is inversion of fliter OR
  // csb_deassert
  assign sck_gate_en = ~(filter | csb_deassert);

  // Bitcnt counter
  /// Bitcnt increases until it hit the max value then wait reset.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bitcnt <= '0;
    end else if (bitcnt != '1) begin
      bitcnt <= bitcnt + MetaBitCntW'(1);
    end
  end

  // Latch only two bits at 7th cmd opcode
  logic cmd_7th; // 7th beat of transaction
  logic cmd_8th; // in 8th beat of transaction
  logic [1:0] cmd_filter;

  assign cmd_7th = (bitcnt == MetaBitCntW'(6));
  assign cmd_8th = (bitcnt == MetaBitCntW'(7));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cmd_filter <= 2'b 00;
    end else if (cmd_7th) begin
      // In this 7th beat, cmd_filter latches 2 bits from cfg_cmd_filter_i
      // This reduces the last filter datapath from muxing 256 to just mux2
      //
      // If below syntax does not work, it can be replaced with
      // for (int unsigned i = 0 ; i < 128 ; i++) begin
      //   it (i == opcode[6:0]) cmd_filter <= cfg_cmd_filter_i[2*i+:2];
      // end
      cmd_filter <= cfg_cmd_filter_i[{opcode_d[6:0],1'b0}+:2];
    end
  end

  // Command Info Latch
  cmd_info_t       cmd_info, cmd_info_d;
  cmd_info_t [1:0] cmd_info_7th, cmd_info_7th_d;

  logic [AddrCntW-1:0] addr_size_d;

  logic cmd_info_latch;

  // Search opcode @ 7th opcode
  always_comb begin
    cmd_info_7th_d = {CmdInfoInput, CmdInfoInput};
    if (cmd_7th) begin
      for(int unsigned i = 0 ; i < NumCmdInfo ; i++) begin
        if (cmd_info_i[i].valid) begin
          if (cmd_info_i[i].opcode == {opcode_d[6:0], 1'b1}) begin
            cmd_info_7th_d[1] = cmd_info_i[i];
          end else if (cmd_info_i[i].opcode == {opcode_d[6:0], 1'b0}) begin
            cmd_info_7th_d[0] = cmd_info_i[i];
          end
        end // cmd_info_i[i].valid
      end
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cmd_info_7th <= '0;
    end else if (cmd_7th) begin
      // Search two candidate among NumCmdInfo. If only one matched, other
      // cmd_info is Always Input command.
      cmd_info_7th <= cmd_info_7th_d;
      //cmd_info_7th <= {PassThroughCmdInfo[{opcode_d[6:0],1'b1}],
      //                 PassThroughCmdInfo[{opcode_d[6:0],1'b0}]};
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cmd_info <= '0;
    end else if (cmd_info_latch) begin
      // Latch only two cmd_info when the 7th bit arrives. Then select among two
      // at the 8th beat for cmd_info_d to reduce timing.
      cmd_info <= cmd_info_d;
    end
  end

  // Some of the fields of cmd_info are used in the big FSM below. The opcode field and the addr_*
  // fields are ignored because we pick them from cmd_info_d instead (in a different FSM state). We
  // rely on the synthesis tool not to generate the unneeded flops but must explicitly waive lint
  // warnings about unused fields.
  logic unused_cmd_info_fields;
  assign unused_cmd_info_fields = &{
    1'b0,
    cmd_info.valid, // valid bit is checked before latching into cmd_info
    cmd_info.opcode,
    cmd_info.addr_en,
    cmd_info.addr_swap_en,
    cmd_info.addr_4b_affected,
    cmd_info.payload_swap_en,
    cmd_info.opcode,
    cmd_info.upload,
    cmd_info.busy
  };

  always_comb begin
    cmd_info_d = '0;
    addr_size_d = AddrCntW'(23);

    if (cmd_8th) begin
      // Latch only two cmd_info when the 7th bit arrives. Then select among two
      // at the 8th beat for cmd_info_d to reduce timing.
      cmd_info_d = cmd_info_7th[host_s_i[0]];
      // TODO: Addr size
      if (cmd_info_7th[host_s_i[0]].addr_4b_affected) begin
        addr_size_d = (cfg_addr_4b_en_i)
                    ? AddrCntW'(31) : AddrCntW'(23);
      end
      cmd_info_d.opcode = opcode_d;

      // dummy_size is set inside State Machine
    end
  end

  // Address swap
  logic addr_set;
  logic addr_phase, addr_phase_outclk;
  assign addr_phase = (st == StAddress);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addrcnt <= '0;
    end else if (addr_set) begin
      // When addr_set is 1, cmd_info is not yet latched.
      `ASSERT_I(AddrSetInStIdle_A, st == StIdle)
      addrcnt <= addr_size_d;
    end else if (addrcnt != '0) begin
      addrcnt <= addrcnt - AddrCntW'(1);
    end
  end

  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) addrcnt_outclk <= '0;
    else         addrcnt_outclk <= addrcnt;
  end

  // Based on AddrCnt, the logic swap.
  // TODO: Handle the DualIO, QuadIO cases
  logic addr_swap;
  assign addr_swap = cfg_addr_mask_i[addrcnt_outclk]
                   ? cfg_addr_value_i[addrcnt_outclk]
                   : host_s_i[0];

  // Address swap should happen in outclk domain.
  // The state machine operates in inclk domain.
  // The state generates mux selection signal.
  // The signal latched in outclk domain then activates the mux.
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) addr_phase_outclk <= 1'b 0;
    else         addr_phase_outclk <= addr_phase;
  end

  // Dummy Counter
  logic dummy_set;
  logic dummycnt_zero;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) dummycnt <= '0;
    else if (dummy_set) begin
      dummycnt <= dummycnt_d;
    end else if (st == StHighZ) begin
      dummycnt <= dummycnt - 1'b 1;
    end
  end
  assign dummycnt_zero = (dummycnt == '0);

  // MByte counter
  logic mbyte_set;
  logic mbytecnt_zero;
  logic [1:0] mbyte_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mbyte_cnt <= '0;
    end else if (mbyte_set) begin
      // TODO: check addr enable and update mbyte_cnt to 3 or 1
      mbyte_cnt <= 2'h 3;
    end else if (st == StMByte) begin
      mbyte_cnt <= mbyte_cnt - 1'b 1;
    end
  end
  assign mbytecnt_zero = (mbyte_cnt == '0);

  // = BEGIN: Passthrough Mux (!important) ====================================

  // As addr_phase_outclk is in outclk domain, addr_swap can be directly used.
  // addr_swap value is also determined by addrcnt_outclk.
  assign passthrough_o.s = (addr_phase_outclk)
                         ? {host_s_i[3:1], addr_swap} : host_s_i;
  logic [3:0] passthrough_s_en;
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) passthrough_s_en <= 4'h 1; // S[0] active by default
    else passthrough_s_en <= device_s_en_inclk;
  end
  assign passthrough_o.s_en = passthrough_s_en;

  assign host_s_o = passthrough_i.s;
  always_ff @(posedge clk_out_i or negedge rst_ni) begin
    if (!rst_ni) host_s_en_o <= '0; // input mode
    else         host_s_en_o <= host_s_en_inclk;
  end

  assign passthrough_o.sck_gate_en = sck_gate_en;
  assign passthrough_o.sck         = host_sck_i;
  assign passthrough_o.sck_en      = 1'b 1;

  // CSb propagation:  csb_deassert signal should be an output of FF or latch to
  // make CSb glitch-free.
  assign passthrough_o.csb_en = 1'b 1;
  assign passthrough_o.csb    = host_csb_i | csb_deassert_outclk ;

  // passthrough_en
  assign passthrough_o.passthrough_en = is_active ;

  // - END:   Passthrough Mux (!important) ------------------------------------

  ///////////////////
  // State Machine //
  ///////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StIdle;
    end else begin
      st <= st_d;
    end
  end

  always_comb begin
    st_d = st;

    // filter
    filter = 1'b 0;

    // Command Cfg Latch
    cmd_info_latch = 1'b 0;

    // addr_set
    addr_set = 1'b 0;

    // mbyte counter udpate
    mbyte_set = 1'b 0;

    // Dummy
    dummy_set = 1'b 0;
    dummycnt_d = '0;

    // Output enable
    host_s_en_inclk   = 4'h 0;
    device_s_en_inclk = 4'h 1; // S[0] MOSI active

    unique case (st)
      StIdle: begin
        if (!is_active) begin
          st_d = StIdle;
        end else if (cmd_8th && cmd_filter[host_s_i[0]]) begin
          st_d = StFilter;
          filter = 1'b 1;

          // Send notification event to SW
        end else if (cmd_8th && cmd_info_d.valid) begin
          cmd_info_latch = 1'b 1;

          // Divert to multiple states.
          //
          // The following states are mainly for controlling the output enable
          // signals. StAddress state, however, controls the SPI lines for
          // address swap in case of Read Commands.
          //
          // Order: addr_en , dummy_en, |payload_en
          // Note that no direct transition to MByte state.
          if (cmd_info_d.addr_en) begin
            st_d = StAddress;

            addr_set = 1'b 1;
          end else if (cmd_info_d.dummy_en) begin
            st_d = StHighZ;

            dummy_set = 1'b 1;
            dummycnt_d = cmd_info_d.dummy_size;
          end else if (cmd_info_d.payload_en != 0) begin
            // Any input/output payload
            if (cmd_info_d.payload_dir == PayloadOut) begin
              st_d = StWait;
            end else begin
              st_d = StDriving;
            end
          end
        end // cmd_8th && cmd_info_d.valid
        else if (cmd_8th) begin
          // cmd_info_d.valid is 0. Skip current transaction
          st_d = StFilter;
          filter = 1'b 1;
        end
      end

      StMByte: begin
        if (mbytecnt_zero) begin
          st_d = StHighZ;

          dummy_set = 1'b 1;
          dummycnt_d = cmd_info_d.dummy_size;
        end else begin
          st_d = StMByte;
        end
      end

      StFilter: begin
        // Command is filtered. Wait until reset(CSb) comes.
        st_d = StFilter;
        host_s_en_inclk   = 4'h 0; // explicit
        device_s_en_inclk = 4'h 0;
      end

      StWait: begin
        // Device Returns Data to host
        st_d = StWait;

        // output enable for host
        host_s_en_inclk = cmd_info.payload_en;
        device_s_en_inclk = 4'h 0;
      end

      StDriving: begin
        // Host sends Data to device
        st_d = StDriving;

        // Output enable for device
        host_s_en_inclk   = 4'h 0; // explicit
        device_s_en_inclk = cmd_info.payload_en;
      end

      StHighZ: begin
        host_s_en_inclk   = 4'h 0; // explicit
        device_s_en_inclk = 4'h 0; // float
        if (dummycnt_zero) begin
          // Assume payload_en not 0
          st_d = (cmd_info.payload_dir == PayloadOut) ? StWait : StDriving;
        end
      end

      StAddress: begin
        // based on state, addr_phase is set. So just check if counter reaches 0
        if (addrcnt == '0) begin
          if (mailbox_hit) begin
            // In Address phase, mailbox region hits. Then Passthrough filteres
            // the command and deligates the control to ReadCmd submodule.
            st_d = StFilter;

            filter = 1'b 1;
          end else if (cmd_info.mbyte_en) begin
            st_d = StMByte;

            mbyte_set = 1'b 1;
          end else if (cmd_info.dummy_en) begin
            st_d = StHighZ;

            dummy_set = 1'b 1;
            dummycnt_d = cmd_info.dummy_size;
          end else if (cmd_info.payload_en != 0) begin
            st_d = (cmd_info.payload_dir == PayloadOut) ? StWait : StDriving;
          end else begin
            // Addr completed command. goto wait state
            st_d = StWait;
          end
        end
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  ///////////////
  // Assertion //
  ///////////////

  // Mailbox hit happens in the middle of Address phase, not at the end of it.
  `ASSERT(MailboxHitConflictAddrCnt_A, mailbox_hit_i |-> (addrcnt != 0))

  // Assume when payload_swap_en is set, the direction is PayloadIn & only
  // Single mode is used
  `ASSUME(PayloadSwapConstraint_M,
    cmd_info.payload_swap_en |-> (cmd_info.payload_en == 4'b 0001)
                              && (cmd_info.payload_dir == PayloadOut))


endmodule: spi_passthrough
