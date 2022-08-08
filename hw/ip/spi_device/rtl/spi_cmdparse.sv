// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Device Flash/ Passthrough mode Command Parser
//
// This module decodes the incoming SPI Flash commands. Then activates proper
// downstream module.

`include "prim_assert.sv"

module spi_cmdparse
  import spi_device_pkg::*;
(
  input clk_i,
  input rst_ni,

  // Data from spi_s2p
  input                     data_valid_i,
  input spi_byte_t          data_i,

  // Configurations
  input spi_mode_e spi_mode_i,

  // Command info slot
  //
  // cmdparse uses the command info slot to activate sub-datapath. It uses
  // pre-assigned index and search opcode. e.g) if cmdslot[0].opcode == 'h03,
  // then if received opcode matches to the cmdslot[0] opcode, then it activates
  // Read Status module as Index 0 is pre-assigned to Read Status.
  input cmd_info_t [NumTotalCmdInfo-1:0] cmd_info_i,

  // control to spi_s2p
  output io_mode_e io_mode_o,

  // Activate downstream modules
  // cmd_info_o is a registered output, latched at 8th posedge SCK
  output sel_datapath_e          sel_dp_o,
  output cmd_info_t              cmd_info_o,
  output logic [CmdInfoIdxW-1:0] cmd_info_idx_o,

  // CFG: Intercept
  input cfg_intercept_en_status_i,
  input cfg_intercept_en_jedec_i,
  input cfg_intercept_en_sfdp_i,

  // Output assumed
  output logic intercept_status_o,
  output logic intercept_jedec_o,
  output logic intercept_sfdp_o,

  // Command Config is not implemented yet.
  // Indicator of command config. The pulse is generated at 3rd bit position
  // of Opcode. The upper 5 bits are used as address to fetch command configs
  // from DPSRAM.
  output logic       cmd_config_req_o,
  output logic [4:0] cmd_config_idx_o
);

  ///////////////
  // Temporary //
  ///////////////
  assign io_mode_o = SingleIO;
  assign cmd_config_req_o = 1'b 0;
  assign cmd_config_idx_o = data_i[4:0];

  // Only opcode in the cmd_info is used. Tie the rest of the members.
  logic unused_cmdinfo_members;
  always_comb begin
    unused_cmdinfo_members = 1'b 0;
    for (int unsigned i = 0 ; i < NumTotalCmdInfo ; i++) begin
      unused_cmdinfo_members ^= ^{ cmd_info_i[i].addr_mode,
                                   cmd_info_i[i].addr_swap_en,
                                   cmd_info_i[i].dummy_en,
                                  ^cmd_info_i[i].dummy_size,
                                   cmd_info_i[i].payload_dir,
                                  ^cmd_info_i[i].payload_en,
                                   cmd_info_i[i].payload_swap_en};
    end
  end

  ////////////////
  // Definition //
  ////////////////
  typedef enum logic [3:0] {
    // At Idle, FSM waits command valid signal.
    // The last 8th bit in the command byte determines the last two bit from
    // `upload_mask`. Then triggers proper downstream modules based on
    // predefined opcode and `upload_mask`.
    StIdle,

    // State machine has state for each downstream module, to track and select
    // proper io_mode and signals
    StStatus,
    StSfdp,
    StJedec,

    // Mailbox is processed in Read Command block.
    StReadCmd,

    StUpload,

    // EN4B/ EX4B fall into this state
    StAddr4B,

    // Write Enable / Disable state
    StWrEn,

    // If opcode does not matched, FSM moves to here and wait the reset.
    StWait
  } st_e;
  st_e st, st_d;

  // spi_flash_cmd_e defines HW supported (TBD for IO) commands.
  // If received SPI Flash command falls into one of these commands, the module
  // processes the command without SW intervention.
  typedef enum logic [7:0] {
    OpReadStatus1 = 'h 05,
    OpReadStatus2 = 'h 35,
    OpReadStatus3 = 'h 15,
    OpReadJEDEC   = 'h 9F,
    OpReadSfdp    = 'h 5A,
    OpReadNormal  = 'h 03,
    OpReadFast    = 'h 0B,
    OpReadDual    = 'h 3B,
    OpReadQuad    = 'h 6B,
    // Supporting DualIO/ QuadIO is TBD.
    OpReadDualIO  = 'h BB,
    OpReadQuadIO  = 'h EB
  } spi_flash_cmd_e;

  ////////////
  // Signal //
  ////////////
  sel_datapath_e sel_dp;
  assign sel_dp_o = sel_dp;
  `ASSERT_KNOWN(SelDpKnown_A, sel_dp_o)

  // FSM asserts latching enable signal for cmd_info in 8th opcode cycle.
  logic                   latch_cmdinfo;
  cmd_info_t              cmd_info_d,     cmd_info_q;
  logic [CmdInfoIdxW-1:0] cmd_info_idx_d, cmd_info_idx_q;

  // the logic operates only when module_active condition is met
  logic module_active;
  logic in_flashmode, in_passthrough;

  // Intercept passthrough if Passthrough is in active
  // As intercept does not affect in Flash mode, the logic ignores
  // `in_passthrough` condition.
  logic intercept_d;

  // below signals are used in the FSM to determine to activate a certain
  // datapath based on the received input (opcode). The opcode is the SW
  // configurable CSRs `cmd_info_i`.
  logic opcode_readstatus, opcode_readjedec, opcode_readsfdp, opcode_readcmd;
  logic opcode_en4b, opcode_ex4b;
  logic opcode_wren, opcode_wrdi;

  always_comb begin
    opcode_readstatus = 1'b 0;
    for (int i = 0 ; i < 3 ; i++) begin
      if (cmd_info_i[CmdInfoReadStatus1+i].valid
        && (data_i == cmd_info_i[CmdInfoReadStatus1+i].opcode)) begin
        opcode_readstatus = 1'b 1;
      end
    end
  end

  assign opcode_readjedec = cmd_info_i[CmdInfoReadJedecId].valid
                          && (data_i == cmd_info_i[CmdInfoReadJedecId].opcode);
  assign opcode_readsfdp = cmd_info_i[CmdInfoReadSfdp].valid
                         && (data_i == cmd_info_i[CmdInfoReadSfdp].opcode);
  assign opcode_en4b = cmd_info_i[CmdInfoEn4B].valid
                     && (data_i == cmd_info_i[CmdInfoEn4B].opcode);
  assign opcode_ex4b = cmd_info_i[CmdInfoEx4B].valid
                     && (data_i == cmd_info_i[CmdInfoEx4B].opcode);
  assign opcode_wren = cmd_info_i[CmdInfoWrEn].valid
                     && (data_i == cmd_info_i[CmdInfoWrEn].opcode);
  assign opcode_wrdi = cmd_info_i[CmdInfoWrDi].valid
                     && (data_i == cmd_info_i[CmdInfoWrDi].opcode);

  always_comb begin
    opcode_readcmd = 1'b 0;
    for (int unsigned i = CmdInfoReadCmdStart ; i <= CmdInfoReadCmdEnd ; i++) begin
      if (cmd_info_i[i].valid && data_i == cmd_info_i[i].opcode) begin
        opcode_readcmd = 1'b 1;
      end
    end
  end

  // cmd_info latch
  // TODO: This can be furthur optimized. At 7th beat, check the opcode[7:1]
  // with cmd_info[NumCmdInfo-1:0].opcode[7:1]. Unless SW configures more than
  // one cmd_info slots with same opcode, at most two slots match with the
  // opcode[7:1]. The two can be latched then at 8th beat, only the last bit
  // of the opcode in the two cmd_info entries can be compared.
  //
  // It reduces the logic from 8bit compare with 24 logic depth into 1bit
  // compare with 1 logic depth.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cmd_info_q <= '{
        payload_dir: payload_dir_e'(PayloadIn),
        addr_mode: addr_mode_e'(0),
        default: '0
      };
      cmd_info_idx_q <= '0;
    end else if (latch_cmdinfo) begin
      cmd_info_q     <= cmd_info_d;
      cmd_info_idx_q <= cmd_info_idx_d;
    end
  end

  always_comb begin
    cmd_info_d = '{
      payload_dir: payload_dir_e'(PayloadIn),
      addr_mode: addr_mode_e'(0),
      default: '0
    };
    cmd_info_idx_d = '0;
    if ((st == StIdle) && module_active && data_valid_i) begin
      for (int unsigned i = 0 ; i < NumTotalCmdInfo ; i++ ) begin
        if (cmd_info_i[i].valid && (data_i == cmd_info_i[i].opcode)) begin
          cmd_info_d     = cmd_info_i[i];
          cmd_info_idx_d = CmdInfoIdxW'(i);
        end
      end
    end
  end

  // cmd_info & cmd_info_idx are registered output in the cmdparse module.
  // The upload module in SPI_DEVICE uses cmd_info to determine if the address
  // field exists or not.

  // The cmd_info value arrives to the rest of the module one clock late. It
  // results in the upload module to assume the command does not have the
  // address field.

  // This commit pulls in the cmd_info one clock early. It leads to longer
  // datapath as cmdparse cannot register the data.
  always_comb begin : cmd_info_output
    cmd_info_o     = cmd_info_q;
    cmd_info_idx_o = cmd_info_idx_q;

    if ((st == StIdle) && module_active && data_valid_i) begin
      cmd_info_o     = cmd_info_d;
      cmd_info_idx_o = cmd_info_idx_d;
    end
  end

  // Check upload field in the cmd_info
  logic upload;
  assign upload = cmd_info_d.upload;

  // Intercept: Latched in SCK
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      intercept_status_o <= 1'b 0;
      intercept_jedec_o  <= 1'b 0;
      intercept_sfdp_o   <= 1'b 0;
    end else if (intercept_d) begin
      if (opcode_readstatus) intercept_status_o <= 1'b 1;
      if (opcode_readjedec)  intercept_jedec_o  <= 1'b 1;
      if (opcode_readsfdp)   intercept_sfdp_o   <= 1'b 1;
    end
  end

  ///////////////////
  // State Machine //
  ///////////////////

  assign in_flashmode   = spi_mode_i == FlashMode ;
  assign in_passthrough = spi_mode_i == PassThrough ;
  assign module_active  = in_flashmode || in_passthrough ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StIdle;
    end else if (module_active) begin
      st <= st_d;
    end
  end

  always_comb begin
    st_d = st;

    sel_dp = DpNone;

    latch_cmdinfo = 1'b 0;

    intercept_d = 1'b 0;

    unique case (st)
      StIdle: begin
        if (module_active && data_valid_i && cmd_info_d.valid) begin
          // 8th bit is valid here
          latch_cmdinfo = 1'b 1;

          priority case (1'b 1)
            opcode_readstatus: begin
              if (in_flashmode) begin
                st_d = StStatus;
              end else if (cfg_intercept_en_status_i) begin
                st_d = StStatus;
                intercept_d = 1'b 1;
              end else begin
                st_d = StWait;
              end
            end

            opcode_readjedec: begin
              if (in_flashmode) begin
                st_d = StJedec;
              end else if (cfg_intercept_en_jedec_i) begin
                st_d = StJedec;
                intercept_d = 1'b 1;
              end else begin
                st_d = StWait;
              end
            end

            // Read SFDP may combine with Read command later
            opcode_readsfdp: begin
              if (in_flashmode) begin
                st_d = StSfdp;
              end else if (cfg_intercept_en_sfdp_i) begin
                st_d = StSfdp;
                intercept_d = 1'b 1;
              end else begin
                // Check passthrough
                st_d = StWait;
              end
            end

            opcode_readcmd: begin
              // Let it move to ReadCmd regardless of the modes
              // Then, ReadCmd will handle Mailbox command if received address
              // falls into Mailbox address range
              st_d = StReadCmd;
            end

            upload: begin
              st_d = StUpload;

              // Reason to select dp here is for Opcode-only commands such as
              // ChipErase. As no further SCK is given after 8th bit, need to
              // write the command to FIFO at the same cycle.
              //
              // May sel_dp have glitch. As Opcode isn't yet fully stable, it
              // has a chance to select datapath to Upload and back to None.
              // If we can write opcode in negedge of SCK, then selecting DP
              // at 8th posedge of SCK is also possible.
              //
              // If not, then we may end up latch `sel_dp` at negedge of SCK.
              // Then when 8th bit is visible here (`data_valid_i`), the
              // sel_dp may change. But the output of sel_dp affects only when
              // 8th negedge of SCK.

              sel_dp = DpUpload;
            end

            opcode_en4b, opcode_ex4b: begin
              st_d = StAddr4B;

              // opcode only commands. Need to assert DP before transition
              sel_dp = (opcode_en4b) ? DpEn4B : DpEx4B ;
            end

            opcode_wren, opcode_wrdi: begin
              st_d = StWrEn;

              // opcode only commands. Need to assert DP before transition
              sel_dp = (opcode_wren) ? DpWrEn : DpWrDi ;
            end

            default: begin
              st_d = StWait;

              // DpNone
            end
          endcase
        end // if (module_active && data_valid_i && cmd_info_d.valid)
        else if (module_active && data_valid_i) begin
          // Could not find valid command information entry.
          st_d = StWait;
        end // if (module_active && data_valid_i)
      end

      // dead-end states below. Reset (CSb de-assertion) let SM back to Idle
      StStatus:  sel_dp = DpReadStatus;

      StJedec:   sel_dp = DpReadJEDEC;

      StSfdp:    sel_dp = DpReadSFDP;

      StReadCmd: sel_dp = DpReadCmd;

      StUpload:  sel_dp = DpUpload;

      StAddr4B: sel_dp = DpNone; // Terminal state wait reset

      StWrEn: sel_dp = DpNone; // Terminal state wait reset

      StWait: begin
        st_d = StWait;

        sel_dp = DpNone;
      end

      default: begin
        sel_dp = DpNone;

        st_d = StIdle;
      end
    endcase

  end
  `ASSERT_KNOWN(StKnown_A, st)


  ///////////////
  // Assertion //
  ///////////////

  // at the first byte, only one datapath shall be active or stay silent.
  `ASSERT(OnlyOneDatapath_A, module_active && data_valid_i && (st == StIdle)
          |-> $onehot0({opcode_readstatus, opcode_readjedec, opcode_readsfdp,
                        opcode_readcmd}))

endmodule
