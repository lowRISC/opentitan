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
  import i3c_hci_pkg::*;
  import i3c_pkg::*;
#(
  // Number of blocked address settings supported.
  parameter int unsigned NumBlocked = i3c_pkg::NumBlocked
) (
  // No requirement for clock or reset.

  // Current command state.
  // - some Command Descriptors require multiple processing phases, separated by a repeated start
  //   (Sr) or HDR Restart; state information from earlier phases must be preserved.
  input  i3c_ctrl_cmd_state_t       cmd_state_i,
  // DAT entry for device-dependent properties.
  input  i3c_dat_mem_t              dat_entry_i,

  // Command Descriptor from the Command Queue.
  input                      [63:0] cmd_queue_i,  // 2 DWORDs.

  // Configuration.
  input                             use_bcst_addr_i,
  input                       [6:0] addr_blocked_i[NumBlocked],
  input                       [6:0] mask_blocked_i[NumBlocked],

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
  output logic                      err_o,

  // Indicates that the Command Phase shall not proceed because the addressed Target is blocked.
  output logic                      blocked_o

  // Additional information presented in the Controller-side registers may be of diagnostic use.
  // TODO(#31307): Supply additional information?
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
    unique case (cmd_reg_o.cmd_attr)
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
    unique case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer:    init_ok_o = init_ok_o & !cmd_imm_o.rnw;  // Write Transfers only.
      // Any CCC command having just a Defining Byte and no data payload shall be sent as an
      // Immediate Data Transfer Command.
      CmdAttr_RegTransfer:    init_ok_o = init_ok_o & |cmd_reg_o.data_length;
      CmdAttr_ComboTransfer:  init_ok_o = init_ok_o & |cmd_combo_o.data_length;
      // Address Assignment Commands support SETDASA and ENTDAA, but not SETAASA (HCI 8.4.1).
      CmdAttr_AddrAssignment: init_ok_o = init_ok_o & (cmd_daa_o.cmd inside {ENTDAA, SETDASA});
      CmdAttr_InternalCtrl:
        unique case (cmd_intn_o.mipi_cmd)
          MIPICmd_NoOp,
          MIPICmd_BroadAddrEnable: init_ok_o = 1'b1;
          MIPICmd_TargRstPattern:
            init_ok_o = (cmd_intn_o.mipi_reserved[13:12] != RstOpType_Reserved);
          MIPICmd_CtrlSDARecovery,
          // TODO(#31308): We need to block the use of CtrlHandOff if not in the 'transition period'
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
    unique case (cmd_reg_o.cmd_attr)
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
    cmd_attrs_o.data_len = 16'b0;

    // Index to DAT is at the same position for the majority of command descriptors.
    cmd_attrs_o.dev_index = cmd_reg_o.dev_index;
    // Most commands have just a single phase.
    cmd_attrs_o.reps_left = '0;

    // Default to acceptance, unless it's a CCC that's prohibited in Command Descriptors (TCRI 6.2).
    err_o = cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_imm_o.cmd);

    // The most significant field is the command type (`cmd_attr`).
    // - the validity of fields is type-specific.
    unique case (cmd_reg_o.cmd_attr)
      CmdAttr_ImmTransfer: begin
        cmd_attrs_o.has_defb = (cmd_imm_o.dtt > 'h4);
        cmd_attrs_o.defb     =  cmd_imm_o.data_byte_1;
        unique case (cmd_imm_o.dtt)
          // Data length does _not_ include the Defining Byte.
          3'h5, 3'h6, 3'h7: cmd_attrs_o.data_len = 16'(cmd_imm_o.dtt - 3'h5);
          default:          cmd_attrs_o.data_len = 16'(cmd_imm_o.dtt);
        endcase
        if (cmd_imm_o.rnw) err_o = 1'b1;  // Immediate transfers are Write only.
        // Not all Transfer mode values are valid/supported.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c)) err_o = 1'b1;
      end
      CmdAttr_RegTransfer: begin
        cmd_attrs_o.has_defb = cmd_reg_o.dbp;
        cmd_attrs_o.defb     = cmd_reg_o.def_byte;
        cmd_attrs_o.data_len = cmd_reg_o.data_length;
        // Not all Transfer mode values are valid/supported, and zero-length transfers shall be done
        // using Immediate Data Transfer commands.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c) || ~|cmd_reg_o.data_length) begin
          err_o = 1'b1;
        end
        if (cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_reg_o.cmd)) err_o = 1'b1;
      end
      CmdAttr_ComboTransfer: begin
        // TODO(#31304). Combo Transfer Commands are declared as unsupported, and not implemented.
        cmd_attrs_o.data_len  = cmd_combo_o.data_length;
        // There are two phases to a Combo Transfer command.
        cmd_attrs_o.reps_left = CmdRepW'(!cmd_state_i.rep_start);
        // Not all Transfer mode values are valid/supported, and zero-length transfers are invalid.
        if (!mode_supported(cmd_attrs_o.mode, cmd_attrs_o.i2c) || ~|cmd_combo_o.data_length ||
            &cmd_combo_o.dlp) begin
          // DATA_LENGTH_POSITION of 2'b3 is "Don't use."
          err_o = 1'b1;
        end
        if (cmd_attrs_o.is_ccc & tcri_blocked_ccc(cmd_combo_o.cmd)) err_o = 1'b1;
      end
      CmdAttr_AddrAssignment: begin
        cmd_attrs_o.mode = XferMode_SDR0;
        cmd_attrs_o.i2c  = 1'b0;
        cmd_attrs_o.toc  = 1'b0;
        // TODO(#31304): Dynamic address during the write phase, but this is possibly not required.
        cmd_attrs_o.data_len  = 'h1;
        // The first segment is a write operation, sending the CCC.
        // Subsequent segments are predominantly reads, collecting the target characteristics,
        // and then transparently changing to a write mid-segment.
        cmd_attrs_o.rnw       = cmd_state_i.rep_start;
        // The index into the DAT advances for each command phase, and is incremented _before_ use.
        cmd_attrs_o.dev_index = cmd_state_i.rep_start ? (cmd_state_i.dev_index + 'b1)
                                                      : (cmd_daa_o.dev_index   - 'b1);
        // Number of repetitions left after the current command phase.
        // Note: there's an initial command phase in which no device is accessed.
        cmd_attrs_o.reps_left = cmd_state_i.rep_start ? (cmd_state_i.reps_left - 'b1)
                                                      : cmd_daa_o.dev_count;
      end
      CmdAttr_InternalCtrl:
        unique case (cmd_intn_o.mipi_cmd)
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
    cmd_attrs_o.brd_ccc = cmd_attrs_o.is_ccc & broadcast_ccc(cmd_attrs_o.ccc);
  end

  // Determine the address to be used for this command phase and whether communication with that
  // address has been blocked.
  always_comb begin : gen_addr
    logic [NumBlocked:0] addr_blocked;  // One extra for the invalid I3C addresses.
    logic [6:0] addr_cand;

    // Using I3C Broadcast Address to commence a transfer?
    // - do NOT use the I3C Broadcast Address after a Repeated Start (Sr); for either CCC or Private
    //   transfers. TODO(#31304): ENTDAA is an exception here.
    cmd_attrs_o.addr_bcst = |{cmd_attrs_o.is_ccc, cmd_attrs_o.ddr, use_bcst_addr_i} &
                             ~cmd_state_i.rep_start;

    // Candidate Target/Group/I3C Broadcast Address.
    /// - I3C Broadcast address is used for SDR Private Transfers iff explicitly requested.
    addr_cand = dat_entry_i.dynamic_address[22:16];
    if (cmd_attrs_o.addr_bcst) begin
      addr_cand = Addr_Broadcast;
    end else begin
      // SETDASA is always sent to the programmed static address, and I2C devices have only static
      // addresses.
      if (cmd_attrs_o.ccc == SETDASA || cmd_attrs_o.i2c) begin  // HCI 6.3.1
        addr_cand = dat_entry_i.static_address;
      end
    end

    // Test whether this is _always_ an invalid address for the Controller to access, prohibited
    // by the I3C spec
    addr_blocked[NumBlocked] = invalid_addr(addr_cand, 1'b0);

    // Address blocking prevents addressing of software-blacklisted addresses, e.g., I2C Targets
    // that may try to employ clock stretching.
    for (int unsigned b = 0; b < NumBlocked; b++) begin
      addr_blocked[b] = ((addr_cand & mask_blocked_i[b]) == addr_blocked_i[b]);
    end

    // Indicate to the core FSM logic that the transfer shall not proceed.
    // TODO(#31304): A later revision separates the address used in the header from the checked
    // address:
    // - there is scant reason to check the I3C Broadcast Address, but we _do_ want to check the
    //   ensuing Target/Group address, and the DA being assigned in Addr Assignment commands.
    // - address blocking is not appropriate for MIPI Internal Control Commands.
    blocked_o = |addr_blocked;
    // Address to be used, as required by CmdArb/CmdAddr, _iff not blocked_.
    // - always W for I3C Broadcast Address) TODO(#31304): ENTDAA is an exception here.
    cmd_attrs_o.addr_rnw = {addr_cand, cmd_attrs_o.rnw & ~cmd_attrs_o.addr_bcst};
  end

  // Signals that the logic does not use (yet).
  // - fields of the shared command state and DAT entry structs that the decoder does not need.
  logic unused_decode_inputs;
  assign unused_decode_inputs = ^{cmd_state_i.available, cmd_state_i.retry_cnt,
                                  cmd_state_i.rst_csect, cmd_state_i.started,
                                  dat_entry_i.autocmd_hdr_code, dat_entry_i.autocmd_mask,
                                  dat_entry_i.autocmd_mode, dat_entry_i.autocmd_value,
                                  dat_entry_i.crr_reject, dat_entry_i.dynamic_address,
                                  dat_entry_i.ibi_payload, dat_entry_i.ibi_reject,
                                  dat_entry_i.ring_id, dat_entry_i.static_address,
                                  dat_entry_i.ts};

endmodule
