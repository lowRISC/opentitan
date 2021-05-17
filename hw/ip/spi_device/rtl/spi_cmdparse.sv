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

  // 256b indicator determines which commands to be uploaded
  // If 1 and the command does not fall into other modules
  // (SFDP/JEDEC/Read/etc), Command Processor triggers upload module.
  // Other upload related configurations (Address/ Payload) are used
  // in upload module.
  //
  // If Command Config (from DPSRAM) is implemented, this signal shall be
  // changed to 8bit width.
  input logic [255:0] upload_mask_i,

  // Command info slot
  //
  // cmdparse uses the command info slot to activate sub-datapath. It uses
  // pre-assigned index and search opcode. e.g) if cmdslot[0].opcode == 'h03,
  // then if received opcode matches to the cmdslot[0] opcode, then it activates
  // Read Status module as Index 0 is pre-assigned to Read Status.
  input cmd_info_t [spi_device_reg_pkg::NumCmdInfo-1:0] cmd_info_i,

  // control to spi_s2p
  output io_mode_e io_mode_o,

  // Activate downstream modules
  output sel_datapath_e sel_dp_o,
  output spi_byte_t     opcode_o,

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

  // among the command slots, Passthrough related slots are not used. So tie them down here.
  logic unused_cmdinfo;
  assign unused_cmdinfo = &{1'b0,
    cmd_info_i[CmdInfoPassthroughEnd:CmdInfoPassthroughStart]};

  // Only opcode in the cmd_info is used. Tie the rest of the members.
  logic unused_cmdinfo_members;
  always_comb begin
    unused_cmdinfo_members = 1'b 0;
    for (int unsigned i = 0 ; i <= CmdInfoPassthroughEnd ; i++) begin
      unused_cmdinfo_members &= &{ cmd_info_i[i].addr_4b_affected,
                                   cmd_info_i[i].addr_en,
                                   cmd_info_i[i].addr_swap_en,
                                   cmd_info_i[i].dummy_en,
                                  &cmd_info_i[i].dummy_size,
                                   cmd_info_i[i].payload_dir,
                                  &cmd_info_i[i].payload_en};
    end
  end

  // Unnecessary but for ascentlint error only
  logic unused_cmdinfo_opcode;
  always_comb begin
    unused_cmdinfo_opcode = 1'b 0;
    for (int unsigned i = CmdInfoPassthroughStart ; i <= CmdInfoPassthroughEnd ; i++) begin
      unused_cmdinfo_opcode &= &cmd_info_i[i].opcode;
    end
  end


  ////////////////
  // Definition //
  ////////////////
  typedef enum logic [2:0] {
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

    StUpload
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

  // the logic operates only when module_active condition is met
  logic module_active;
  logic in_flashmode, in_passthrough;

  // Opcode out
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      opcode_o <= spi_byte_t'(0);
    end else if (st == StIdle && data_valid_i) begin
      opcode_o <=  data_i;
    end
  end

  // below signals are used in the FSM to determine to activate a certain
  // datapath based on the received input (opcode). The opcode is the SW
  // configurable CSRs `cmd_info_i`.
  logic opcode_readstatus, opcode_readjedec, opcode_readsfdp, opcode_readcmd;

  assign opcode_readstatus = (data_i == cmd_info_i[CmdInfoReadStatus1].opcode)
                           | (data_i == cmd_info_i[CmdInfoReadStatus2].opcode)
                           | (data_i == cmd_info_i[CmdInfoReadStatus3].opcode);
  assign opcode_readjedec = (data_i == cmd_info_i[CmdInfoReadJedecId].opcode);
  assign opcode_readsfdp = (data_i == cmd_info_i[CmdInfoReadSfdp].opcode);

  always_comb begin
    opcode_readcmd = 1'b 0;
    for (int unsigned i = CmdInfoReadCmdStart ; i <= CmdInfoReadCmdEnd ; i++) begin
      if (data_i == cmd_info_i[i].opcode) opcode_readcmd = 1'b 1;
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
      // TODO: What condition should this to be activated?
      st <= st_d;
    end
  end

  always_comb begin
    st_d = st;

    sel_dp = DpNone;

    unique case (st)
      StIdle: begin
        if (module_active && data_valid_i) begin
          // 8th bit is valid here
          priority case (1'b 1)
            opcode_readstatus: begin
              st_d = StStatus;
            end

            opcode_readjedec: begin
              if (in_flashmode) begin
                st_d = StJedec;
              end else begin
                // TODO: Passthrough ?
                st_d = StIdle;
              end
            end

            opcode_readsfdp: begin
              if (in_flashmode) begin
                st_d = StSfdp;
              end else begin
                // TODO: Passthrough? Cannot stay in the Idle as it will compare at the next byte
                st_d = StIdle;
              end
            end

            opcode_readcmd: begin
              // Let it move to ReadCmd regardless of the modes
              // Then, ReadCmd will handle Mailbox command if received address
              // falls into Mailbox address range
              st_d = StReadCmd;
            end

            default: begin
              // If Command Config in DPSRAM, need to change as below
              // if (upload_mask_i[data_i[2:0]]) begin
              if (upload_mask_i[data_i]) begin
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
              end else begin
                st_d = StIdle;

                // DpNone
              end
            end
          endcase
        end
      end

      // dead-end states below. Reset (CSb de-assertion) let SM back to Idle
      StStatus:  sel_dp = DpReadStatus;

      StJedec:   sel_dp = DpReadJEDEC;

      StSfdp:    sel_dp = DpReadSFDP;

      StReadCmd: sel_dp = DpReadCmd;

      StUpload:  sel_dp = DpUpload;

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
