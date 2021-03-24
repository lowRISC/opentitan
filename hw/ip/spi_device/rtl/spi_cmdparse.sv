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
          unique case (data_i) inside
            OpReadStatus1, OpReadStatus2, OpReadStatus3: begin
              // Always handled by internal Status
              // regardless of FlashMode/ PassThrough
              st_d = StStatus;

            end

            OpReadJEDEC: begin
              // Let it move to Jedec when FlashMode
              if (in_flashmode) begin
                st_d = StJedec;

              end else begin
                // PassThrough
                st_d = StIdle;
              end
            end

            OpReadSfdp: begin
              if (in_flashmode) begin
                st_d = StSfdp;
              end else begin
                // PassThrough
                st_d = StIdle;
              end
            end

            OpReadNormal, OpReadFast, OpReadDual, OpReadQuad, OpReadDualIO, OpReadQuadIO: begin
              // Let it move to ReadCmd regardless of the modes
              // Then, ReadCmd will handle Mailbox command if received address
              // falls into Mailbox address range
              st_d = StReadCmd;

              // Does not set Datapath to Read Command yet. As Read command
              // processing block can be active after 8th edge of SCK.
              //sel_dp = DpReadCmd;
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

endmodule
