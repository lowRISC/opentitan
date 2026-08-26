// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// A purely-combinational module to validate the Command Descriptor and extract fields/properties
// that are required during command execution.
//
// We are required to detect any 'illegal or invalid combination of fields' in Command Descriptors
// (TCRI 6.4.1.10).

module i3c_cmd_decode
  import i3c_consts_pkg::*;
  import i3c_controller_pkg::*;
  import i3c_pkg::*;
#(
  // Number of entries in the Device Address Table.
  parameter int unsigned NumDATEntries = i3c_pkg::NumDATEntries,

  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries)
) (
  // No requirement for clock or reset.

  // Current command state.
  // - some Command Descriptors require multiple processing phases, separated by a repeated start
  //   (Sr) or HDR Restart; state information from earlier phases must be preserved.
  input  i3c_ctrl_cmd_state_t       cmd_state_i,
  // DAT entry for device-dependent properties.
  input  i3c_dat_mem_t              dat_entry_i,

  // Command Descriptor from the Command Queue.
  input  logic               [63:0] cmd_queue_i,  // 2 DWORDs.

  // Interpretations of the Command Descriptor.
  output i3c_xfer_cmd_intern_ctrl_t cmd_intn_o,   // Internal Control commands.
  output i3c_xfer_cmd_addr_assgn_t  cmd_daa_o,    // Address Assignment commands.
  output i3c_xfer_cmd_combo_t       cmd_combo_o,  // Combo commands.
  output i3c_xfer_cmd_reg_t         cmd_reg_o,    // Regular commands.
  output i3c_xfer_cmd_imm_t         cmd_imm_o,    // Immediate commands.

  // Initial validity check of a Command Descriptor.
  output logic                      init_ok_o,

  // Properties of the Command Descriptor, derived from `cmd_raw` combinationally.
  output i3c_ctrl_cmd_attrs_t       cmd_attrs_o,

  // Indicates that the Command Descriptor is invalid for one or more reasons;
  // - the TCRI permits only 'NotSupported' in response to an invalid command.
  output logic                      err_o

  // Additional information presented in the Controller-side registers may be of diagnostic use.
  // TODO: Supply additional information?
);

  // This is likely to be required once we are selecting the input command from multiple sources.
  // - Auto Command support is expected to be included in a later revision.
  // - Scheduled Commands are presently not supported, but they too would be handled here.
  wire [63:0] cmd_raw = cmd_queue_i;

  // Reinterpret the raw Command Descriptor as each supported type of command.
  // - `cmd_reg_o` is a useful way to access fields that are common to most/all command types.
  assign cmd_intn_o  = i3c_xfer_cmd_intern_ctrl_t'(cmd_raw);
  assign cmd_daa_o   = i3c_xfer_cmd_addr_assgn_t'(cmd_raw);
  assign cmd_combo_o = i3c_xfer_cmd_combo_t'(cmd_raw);
  assign cmd_imm_o   = i3c_xfer_cmd_imm_t'(cmd_raw);
  assign cmd_reg_o   = i3c_xfer_cmd_reg_t'(cmd_raw);

  // HDR-DDR mode?
  // - `device` field of DAT entry: 0 = I3C, 1 = I2C (HCI Table 130).
  // - may be trusted only once the `cmd_attr` field has been checked.
  wire hdr_ddr = (cmd_reg_o.mode == XferMode_HDRDDR) & !dat_entry_i.device;

  // The decision on the validity of the command must be performed before commencing command
  // dispatch, because the dispatch decision depends upon the validity of certain command fields.
  //
  // If the initial checks pass, the following fields of `cmd_imm_o`, `cmd_reg_o` and `cmd_combo_o`
  // may then be trusted:
  //   - `attr`
  //   - `data_length`
  //
  // These are important for the dispatch decision, and rejecting invalid commands that would
  // otherwise deadlock the Controller and Driver.
  always_comb begin
    // Is this a Common Command Code transfer?
    case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer,
      CmdAttr_RegTransfer: begin
        // HCI version 1.2 supports CCC Framing in SDR only (not HDR modes), but the CMD field may
        // be valid for HDR-DDR transfers too, so CP requires qualification here.
        // - `device` field of DAT entry: 0 = I3C, 1 = I2C (HCI Table 130).
        cmd_attrs_o.is_ccc = cmd_reg_o.cp & !hdr_ddr;
      end
      // Combo Transfers do not support CCCs (TCRI Table 10).
      CmdAttr_ComboTransfer:  cmd_attrs_o.is_ccc = 1'b0;
      CmdAttr_AddrAssignment: cmd_attrs_o.is_ccc = 1'b1;
      default: cmd_attrs_o.is_ccc = 1'b0;
    endcase
    // Some CCCs are prohibited in Command Descriptors (TCRI 6.2).
    init_ok_o = !(cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_reg_o.cmd));

    // Initial dispatch checks based on the type of Command Descriptor.
    case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer:    init_ok_o = init_ok_o & !cmd_imm_o.rnw;  // Write Transfers only.
      // Any CCC command having just a Defining Byte and no data payload shall be sent as an
      // Immediate Data Transfer Command.
      CmdAttr_RegTransfer:    init_ok_o = init_ok_o & |cmd_reg_o.data_length;
      CmdAttr_ComboTransfer:  init_ok_o = init_ok_o & |cmd_combo_o.data_length;
      // Address Assignment Commands support SETDASA and ENTDAA, but not SETAASA (HCI 8.4.1).
      CmdAttr_AddrAssignment: init_ok_o = init_ok_o & (cmd_daa_o.cmd inside {ENTDAA, SETDASA});
      CmdAttr_InternalCtrl:
        case (cmd_intn_o.mipi_cmd)
          MIPICmd_NoOp,
          MIPICmd_BroadAddrEnable: init_ok_o = 1'b1;
          MIPICmd_TargRstPattern:
            init_ok_o = (cmd_intn_o.mipi_reserved[13:12] != RstOpType_Reserved);
          MIPICmd_CtrlSDARecovery,
          // TODO: We need to block the use of CtrlHandOff if not in the 'transition period'
          MIPICmd_CtrlHandoff,
          MIPICmd_AttemptDBR:  /* Nothing to do */;
          MIPICmd_EndXferHDR:
            // Only the HDR-DDR setting is supported.
            init_ok_o = (cmd_intn_o.mipi_reserved[15:12] == 4'h1);
          // These commands are for DMA mode only:
          // - MIPICmd_RingBundleLock, MIPICmd_DevCtxUpdate.
          default: init_ok_o = 1'b0;  // Includes invalid/undefined sub-commands.
        endcase
      default: init_ok_o = 1'b0;  // Invalid/undefined Command Descriptor types.
    endcase
  end

  // Decoding of additional command information may depend upon the current command state and
  // any DAT entry that has just been read.
  // - this logic may assume that the basic validity checks above (`init_ok_o`) have passed.
  always_comb begin
    // This field specifies the type of the Command Descriptor, and thus determines the validity
    // of all other fields.
    cmd_attrs_o.attr = cmd_reg_o.cmd_attr;  // Same location for ALL Command Descriptors.

    // CCC/CMD for the basic command types.
    cmd_attrs_o.ccc  = cmd_reg_o.cmd;
    // Transaction ID for the basic command types.
    cmd_attrs_o.tid  = cmd_reg_o.tid;
    // WRite On Completion for the basic command types.
    cmd_attrs_o.wroc = cmd_reg_o.wroc;
    // Transfer mode, for the basic command types.
    cmd_attrs_o.mode = cmd_reg_o.mode;
    // I2C rather than I3C device, for the basic command types.
    cmd_attrs_o.i2c  = dat_entry_i.device;  // 0 = I3C, 1 = I2C (HCI Table 130).
    // Use HDR-DDR mode for this command?
    cmd_attrs_o.ddr  = hdr_ddr;

    // Determine maximum number of retries; this depends upon the device properties as well.
    case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer,
      CmdAttr_RegTransfer,
      CmdAttr_ComboTransfer: begin
        // Direct CCCs support at least a single retry count to allow the Target more time to
        // respond; the DAT entry may indicate a larger number of retries in this case too.
        if (cmd_attrs_o.is_ccc) begin
          if (direct_get(cmd_reg_o.cmd)) begin
            cmd_attrs_o.retry_cnt =
              dat_entry_i.dev_nack_retry_cnt[30] ? dat_entry_i.dev_nack_retry_cnt : 2'b01;
          end else cmd_attrs_o.retry_cnt = 2'b00;
        end else cmd_attrs_o.retry_cnt = dat_entry_i.dev_nack_retry_cnt;
      end
      default: cmd_attrs_o.retry_cnt = 2'b00;
    endcase

    cmd_attrs_o.rnw      = cmd_reg_o.rnw;
    cmd_attrs_o.toc      = cmd_reg_o.toc;
    cmd_attrs_o.has_defb = 1'b0;
    cmd_attrs_o.defb     = 8'b0;  // Not needed by default; just avoids latch creation.

    // Index to DAT is at the same position for the majority of command descriptors.
    cmd_attrs_o.dev_index = cmd_reg_o.dev_index;
    // Most commands have just a single phase.
    cmd_attrs_o.reps_left = '0;

    // Default to acceptance, unless it's a CCC that's prohibited in Command Descriptors (TCRI 6.2).
    err_o = cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_imm_o.cmd);

    // The most significant field is the command type (`cmd_attr`).
    // - the validity of fields is type-specific.
    case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer: begin
        cmd_attrs_o.has_defb = (cmd_imm_o.dtt > 'h4);
        cmd_attrs_o.defb     =  cmd_imm_o.data_byte_1;
        if (cmd_imm_o.rnw) err_o = 1'b1;  // Immediate transfers are Write only.
        // Not all Transfer mode values are valid/supported.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c)) err_o = 1'b1;
      end
      CmdAttr_RegTransfer: begin
        cmd_attrs_o.has_defb = cmd_reg_o.dbp;
        cmd_attrs_o.defb     = cmd_reg_o.def_byte;
        // Not all Transfer mode values are valid/supported, and zero-length transfers shall be done
        // using Immediate Data Transfer commands.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c) || ~|cmd_reg_o.data_length) begin
          err_o = 1'b1;
        end
        if (cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_reg_o.cmd)) err_o = 1'b1;
      end
      CmdAttr_ComboTransfer: begin
        // There are two phases to a Combo Transfer command.
        cmd_attrs_o.reps_left = !cmd_state_i.rep_start;
        // Not all Transfer mode values are valid/supported, and zero-length transfers are invalid.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c) || ~|cmd_combo_o.data_length ||
            &cmd_combo_o.dlp) begin
          // DATA_LENGTH_POSITION of 2'b3 is "Don't use."
          err_o = 1'b1;
        end
        if (cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_combo_o.cmd)) err_o = 1'b1;
      end
      CmdAttr_AddrAssignment: begin
        cmd_attrs_o.mode    = XferMode_SDR0;
        cmd_attrs_o.i2c     = 1'b0;
        cmd_attrs_o.toc     = 1'b0;
        // The first segment is a write operation, sending the CCC.
        // Subsequent segments are predominantly reads, collecting the target characteristics,
        // and then transparently changing to a write mid-segment.
        cmd_attrs_o.rnw     = cmd_state_i.rep_start;
        // The index into the DAT advances for each command phase, and is incremented _before_ use.
        cmd_attrs_o.dev_index = cmd_state_i.rep_start ? (cmd_state_i.dev_index + 'b1)
                                                      : (cmd_daa_o.dev_index   - 'b1);
        // Number of repetitions left after the current command phase.
        // Note: there's an initial command phase in which no device is accessed.
        cmd_attrs_o.reps_left = cmd_state_i.rep_start ? (cmd_state_i.reps_left - 'b1)
                                                      : cmd_daa_o.dev_count;
      end
      CmdAttr_InternalCtrl:
        case (cmd_intn_o.mipi_cmd)
          MIPICmd_NoOp,
          MIPICmd_BroadAddrEnable: err_o = 1'b0;
          MIPICmd_TargRstPattern:
            if (cmd_intn_o.mipi_reserved[13:12] == RstOpType_Reserved) begin
              err_o = 1'b1;
            end
          MIPICmd_CtrlSDARecovery,
          MIPICmd_CtrlHandoff,
          MIPICmd_AttemptDBR: begin end // Nothing to do.
          MIPICmd_EndXferHDR:
            // Only the HDR-DDR setting is supported.
            if (cmd_intn_o.mipi_reserved[15:12] != 4'h1) err_o = 1'b1;
          // These commands are for DMA mode only.
          // - MIPICmd_RingBundleLock, MIPICmd_DevCtxUpdate.
          default: err_o = 1'b1;
        endcase
      default: err_o = 1'b1;
    endcase

    // Derived properties.
    cmd_attrs_o.brd_ccc = cmd_attrs_o.is_ccc & !cmd_attrs_o.ccc[7];
  end

endmodule
