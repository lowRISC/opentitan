// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Controller Core state machine for Command/Response processing and handling of bus events
// including In-Band Interrupts.

module i3c_controller_fsm
  import i3c_controller_pkg::*;
  import i3c_fifo_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
#(
  parameter int unsigned ClkFreq       = 50_000_000,
  parameter int unsigned DataWidth     = 32,
  // Number of bits required to express the maximum depth of any FIFO.
  parameter int unsigned FIFODepthW    = i3c_fifo_pkg::DepthW,
  // Number of entries in each of the DAT and the DCT.
  parameter int unsigned NumDATEntries = i3c_pkg::NumDATEntries,
  parameter int unsigned NumDCTEntries = i3c_pkg::NumDCTEntries,
  // Width of DCT entry, in bytes.
  parameter int unsigned DCTMaskW      = $bits(i3c_dct_mem_t) / 8,

  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries),
  localparam int unsigned DCTAddrW = $clog2(NumDCTEntries)
) (
  // Clock and reset for system interface.
  input                       clk_i,
  input                       rst_ni,

  // Control inputs.
  input                       enable_i,
  input                       enable_stby_i,
  input                       sw_reset_i,
  input                       fifo_rst_i[FIFO_Count],
  input  i3c_ctrl_gstate_e    gstate_i,

  // Status outputs.
  output                      inactive_o,
  output                      suspending_o,
  output                      aborted_o,           // Abort request handled.
  output                      transfer_aborted_o,  // One or more transfers aborted.

  // Configuration.
  input  i3c_reg2hw_t         reg2hw_i,
  input  hc_control_t         hc_control_i,  // Implemented as `hwext`.

  // Software writes to the current DCT index.
  input                       dct_idx_qe_i,
  input        [DCTAddrW-1:0] dct_idx_q_i,

  // Blocked device addresses.
  // TODO: Implement this debug/safety functionality.
  input                 [6:0] addr_blocked_i[NumBlocked],
  input                 [6:0] mask_blocked_i[NumBlocked],

  // Software writes to the DAT must update the DAT cache.
  input                 [1:0] sw_datc_we_i,
  input        [DATAddrW-1:0] sw_datc_widx_i,
  input  i3c_datc_wdata_t     sw_datc_wdata_i,

  // Reads from Device Address Table (DAT).
  output                      dat_re_o,
  output       [DATAddrW-1:0] dat_idx_o,
  input  i3c_dat_mem_t        dat_rdata_i,

  // Writes to Device Characteristics Table (DCT).
  output                      dct_we_o,
  output       [DCTAddrW-1:0] dct_idx_o,
  output       [DCTMaskW-1:0] dct_wmask_o,
  output i3c_dct_mem_t        dct_wdata_o,

  // Reads from Command Queue.
  output                      cmd_desc_rready_o,
  input                       cmd_desc_rvalid_i,
  input       [DataWidth-1:0] cmd_desc_rdata_i,

  // Writes to Response Queue.
  output                      rsp_desc_wvalid_o,
  output      [DataWidth-1:0] rsp_desc_wdata_o,
  input                       rsp_desc_wready_i,
  input                       rsp_desc_wfull_i,

  // Reads from Tx Data Buffer.
  output                      txbuf_rready_o,
  input                       txbuf_rvalid_i,
  input       [DataWidth-1:0] txbuf_rdata_i,
  input                       txbuf_rempty_i,
  input        [FIFODepthW:0] txbuf_rused_i,

  // Writes to Rx Data buffer.
  output                      rxbuf_wvalid_o,
  output      [DataWidth-1:0] rxbuf_wdata_o,
  input                       rxbuf_wready_i,
  input                       rxbuf_wfull_i,
  input        [FIFODepthW:0] rxbuf_wavail_i,

  // Writes to In Band Interrupt Queue.
  output                      ibi_data_wvalid_o,
  output      [DataWidth-1:0] ibi_data_wdata_o,
  input                       ibi_data_wready_i,
  input                       ibi_data_wfull_i,

  // Writes to IBI Status Descriptor FIFO.
  output                      ibi_stat_wvalid_o,
  output      [DataWidth-1:0] ibi_stat_wdata_o,
  input                       ibi_stat_wready_i,
  input                       ibi_stat_wfull_i,

  // Broadcast CCCs received in Standby Controller mode.
  input                       stby_bcst_wvalid_i,
  input       [DataWidth-1:0] stby_bcst_wdata_i,
  output                      stby_bcst_wready_o,

  // Start request signaling from Targets.
  input                       trx_sreq_i,

  // Timing parameters; target- and transfer-invariant.
  output         [TmCycW-1:0] tcas_d2_o,
  output         [TmCycW-1:0] tcbp_d2_o,

  // Retrying of NACked commands.
  output                      cmd_nacked_o,
  input                       cmd_retry_i,

  // Request to the transceiver.
  output                      trx_dvalid_o,
  input                       trx_dready_i,
  output i3c_ctrl_trx_req_t   trx_dreq_o,

  // Arbitration outcomes from the transceiver.
  input                       trx_avalid_i,
  input  i3c_ctrl_trx_arb_t   trx_arb_i,
  output                      trx_aready_o,

  // Read data from the transceiver.
  input                       trx_rdvalid_i,
  input  i3c_ctrl_trx_rdata_t trx_rdata_i,

  // Response from the transceiver.
  input                       trx_rvalid_i,
  output                      trx_rready_o,
  input  i3c_ctrl_trx_rsp_t   trx_rsp_i,

  // CE[3:0] error conditions (Table 44).
  output                [3:0] ctrl_error_o,

  // Debug Extended Capability.
  output logic          [5:0] bcl_tfr_ststat_o,
  output                [3:0] cmd_tid_o
);

  import i3c_consts_pkg::*;
  import i3c_ctrl_ccc_pkg::*;

  localparam int unsigned Log2DW = $clog2(DataWidth);

  // The type of transfer being performed.
  // - not all transfers are the result of Command Descriptors; Targets may also initiate transfers.
  // - note also that `cmd_state` is valid only for Command transfers, and that we may have to
  //   handle a non-Command transfer whilst a Command is awaiting a retry.
  // - the transfer type may change in response to losing address arbitration.
  i3c_ctrl_trans_type_e trans_type;

  // We collect the lower half of the Command Descriptor from the FIFO but leave the upper half
  // in place until the command is completed.
  logic                 cmdq_lo_valid;  // Validity indicator; has been retrieved from the FIFO.
  logic [DataWidth-1:0] cmdq_lo_data;   // Lower half (1 DWORD).

   // Current Command from Driver via the Command Queue.
  logic [$bits(i3c_xfer_cmd_imm_t)-1:0] cmd_raw;      // 2 DWORDs.
  assign cmd_raw = {cmd_desc_rdata_i, cmdq_lo_data};  // Current and previous DWORDs.

  // Current Command State.
  i3c_ctrl_cmd_state_t cmd_state;
  logic cmd_complete;

  // Result of command decoding.
  // - we are required to detect any illegal/invalid combination of values in Command Descriptors.
  // - this is valid from `CmdDecode` onwards because it depends upon the Device Address Table entry
  //   as well as the Command Descriptor.
  logic cmd_dec_err;
  // Was the command `Nack`ed too many times?
  logic cmd_nack_excess;

  // Interpretations of the raw Command Descriptor DWORDs.
  i3c_xfer_cmd_intern_ctrl_t cmd_intn;
  i3c_xfer_cmd_addr_assgn_t cmd_daa;
  i3c_xfer_cmd_combo_t cmd_combo;
  i3c_xfer_cmd_reg_t cmd_reg;
  i3c_xfer_cmd_imm_t cmd_imm;

   // Initial dispatch/reject check on commands.
  logic cmd_init_ok;

  // Command Descriptor fields/properties.
  // - derived combinationally from the current Command Descriptor; no additional storage.
  i3c_ctrl_cmd_attrs_t cmd_attrs;

  // Device Address Table entry.
  // - a single command descriptor may involve the reading and use of multiple DAT entries.
  i3c_dat_mem_t dat_entry;

  // Command validation and decoding.
  // - commands come from the Command Queue and - at some point - Auto-Command handling.
  // - Scheduled Commands are presently not implemented at all.
  i3c_cmd_decode u_cmd_decode (
    // Current command state, for phase-dependent command properties.
    .cmd_state_i(cmd_state),
    // Device Address Table entry; the transfer mode depends upon this.
    .dat_entry_i(dat_entry),

    // Raw command descriptor DWORDs from the Command Queue.
    .cmd_queue_i(cmd_raw),

    // Initial validity check of a Command Descriptor.
    .init_ok_o  (cmd_init_ok),

    // Command attributes, derived combinationally from the Command Descriptor.
    .cmd_attrs_o(cmd_attrs),

    // Interpretations of the input Command Descriptor.
    .cmd_intn_o (cmd_intn),
    .cmd_daa_o  (cmd_daa),
    .cmd_combo_o(cmd_combo),
    .cmd_reg_o  (cmd_reg),
    .cmd_imm_o  (cmd_imm),

    // Response status; ErrStatus_OK iff the command is accepted by the decoder.
    .err_o      (cmd_dec_err)
  );

  // Current and next states.
  i3c_ctrl_fsm_state_e state_q, state_d;

  // The first word of any transmission may require special treatment.
  logic txd_imm;
  // The final word of any transfer may require special treatment.
  logic data_last;
  // Any more data?
  logic data_left;
  // Data transfer state.
  logic [15:0] next_len;
  logic [15:0] data_len;
  assign data_left = |data_len;
  assign data_last = (data_len <= 'h4);
  assign next_len  = data_last ? 16'b0 : (data_len - 'h4);
  // Data length for the next transfer.
  wire [1:0] dlen = (|(data_len >> 2) ? 2'b11 : (data_len[1:0] - 2'b01));  // Byte(s).

  // Register state for CCC handling.
  logic [CtrlCRWidth-1:0] reg_state[CtrlCR_Count];

  // CCC Framing information from the previous Command Descriptor.
  wire  [7:0] prev_ccc  = reg_state[CtrlCR_CCC];
  wire  [7:0] prev_defb = reg_state[CtrlCR_DEFB];
  wire    prev_had_defb = reg_state[CtrlCR_Status][CtrlStat_HasDEFB];

  // Do we need to restart the CCC Framing?
  // - must restart if CCC, DEFB or presence/absence of DEFB differs from the previous command;
  //   otherwise the Target(s) shall have retained the framing information.
  wire [16:0] prev_ccc_attribs = {prev_had_defb,      prev_defb,      prev_ccc};
  wire [16:0] cmd_ccc_attribs  = {cmd_attrs.has_defb, cmd_attrs.defb, cmd_attrs.ccc};
  wire ccc_framing_reqd = |{cmd_ccc_attribs ^ prev_ccc_attribs, !cmd_state.rep_start};

  // Start thresholds are specified as being 'at least 2^(N+1)' so a right shift here is cheapest.
  // - we can never be starting both Rx and Tx simultaneously, so we employ MUXing here.
  wire [FIFODepthW:0] buf_words = cmd_attrs.rnw ? rxbuf_wavail_i : txbuf_rused_i;
  wire [2:0] start_thld = cmd_attrs.rnw ? reg2hw_i.data_buffer_thld_ctrl.rx_start_thld.q
                                        : reg2hw_i.data_buffer_thld_ctrl.tx_start_thld.q;
  // Some commands do not require the Tx Buffer.
  wire cmd_no_txd = |{cmd_attrs.attr == CmdAttr_ImmTransfer,
                      cmd_attrs.attr == CmdAttr_RegTransfer && ~|cmd_reg.data_length};
  wire buf_words_enough = ({buf_words, 2'b00} >= cmd_reg.data_length);
  // The start threshold or the data length must be satisfied before the command may be dispatched.
  wire cmd_start  = |{cmd_no_txd, buf_words[FIFODepthW:1] >> start_thld, buf_words_enough};

  // Tx Data for passing to the CCC handling and/or sending to the transceiver.
  logic [DataWidth-1:0] tx_data;
  // Rx Data for passing to the CCC handling and/or writing into the buffer.
  logic [DataWidth-1:0] rx_data;

  // Number of bytes in the current transceiver response.
  localparam int unsigned Log2DBW = Log2DW - 3;
  wire [Log2DBW:0] rx_len = trx_rdata_i.rlen;
  // Track the number of bytes of received data.
  // - this is used for CCC handling, Private Reads _and_ IBI payload reception.
  logic [15:0] rx_data_len;
  wire  [15:0] rx_next_len = rx_data_len + rx_len;

  // Interface to Common Command Code handling.
  i3c_ctrl_ccc_req_t ccc_req;
  i3c_ctrl_ccc_rsp_t ccc_rsp;
  logic [3:0] ccc_idx;

  // Construction of the request to the CCC handling.
  // - data into/out of the CCC handling has the same form/byte ordering as that in the DWORD-based
  //   Tx and Rx buffers, so it is not complicated by the transmission mode/packing.
  always_comb begin
    ccc_req = '0;
    // Tx Buffer data, already in the appropriate order for passing to the transceiver.
    ccc_req.txd_left  = txd_imm | data_left;
    ccc_req.txd_valid = txd_imm | (txbuf_rvalid_i & data_left);
    ccc_req.txd_len   = dlen;
    ccc_req.txd_data  = tx_data;
    // DAT entry for the current Target.
    ccc_req.dat_entry = dat_entry;
    // Index number within the current CCC handling (= local state number, initially 0).
    ccc_req.idx       = ccc_idx;
    // Read data returned from the transceiver.
    ccc_req.re        = trx_rdvalid_i;
    ccc_req.rlen      = rx_len;
    ccc_req.rdata     = rx_data;
    // Raw Command Descriptor.
    ccc_req.cmd_raw   = cmd_raw;
  end

  // Proceed to the next state within the CCC handling, or complete the CCC handling.
  //
  // Note: since the CCC handling logic in `i3c_controller_ccc` is purely combinational, the
  //       `ccc_proceed` signal advances the `idx` value and thus produces a change in the outputs
  //       but this does _not_ imply termination of the CCC command transfer. That is determined
  //       by `ccc_rsp.done` being asserted.
  wire ccc_proceed = &{txbuf_rvalid_i | !ccc_rsp.txd_req,   // Not still waiting on Tx data.
                       trx_dready_i | !ccc_rsp.req_dvalid}; // Not still waiting on transceiver ack.

  // ------------------------------- Arbitration Requests from Targets -----------------------------

  // Start request received from Target?
  logic start_request;
  // Requests from I3C targets.
  // - these are valid only when arbitration has been lost and the FSM is in one of the following
  //   states: WaitArb, WaitAckb, SendAckb, HotJoin, CRR, IBICheck.
  // - although `trx_avalid_i` is asserted only in `WaitArb`, the request data is held stable by
  //   the transceiver logic.
  wire hotjoin_req = !trx_arb_i.ibi & (trx_arb_i.addr == 7'h02);  // Hot-Join address is 7'h02.
  wire cr_role_req = !trx_arb_i.ibi & (trx_arb_i.addr != 7'h02);  // Anything else is a CRR.
  wire ibi_req     =  trx_arb_i.ibi;

  // Whether to reject the Target's request, having looked up its dynamic address in the DAT.
  logic ibi_reject, crr_reject, ibi_payload;
  i3c_xfer_mode_e xfer_mode;

  // Did the most recent Command Transfer, IBI request, Hot-Join or CRR receive a NACK in response?
  logic nacked;
  // Transfer mode for IBI payload fetch.
  i3c_xfer_mode_e ibi_xfer_mode;

  // TODO: Auto-Command behavior is presently not implemented.
  logic [7:0] mdb;
  assign mdb = rx_data[7:0];

  // Auto-Command behavior (HCI 6.11).
  wire autocmd_fetch = ibi_payload & ((mdb & dat_entry.autocmd_mask) == dat_entry.autocmd_value);
  // AUTOCMD_HDR_CODE is sanitized as per HCI 6.11.2 to ensure that it is a Read transfer.
  logic [7:0] autocmd_code;
  assign autocmd_code = dat_entry.autocmd_hdr_code[58] ? dat_entry.autocmd_hdr_code : 8'h80;

  // Command Queue enabled?
  // - software may choose to Run/Stop PIO Command Queue handling at any point.
  // - do not start command processing either when Disabled or when Abort requested.
  wire cmd_enabled = reg2hw_i.pio_control.enable & reg2hw_i.pio_control.rs &
                    !reg2hw_i.pio_control.abort;

  // Requests from the HCI Driver software; Command Descriptors are formed of two DWORDs.
  // Note: although we may know that there _are_ at least two DWORDs, there may be a delay in
  // reading the second.
  wire cmd_avail = &{cmd_enabled, cmdq_lo_valid, cmd_desc_rvalid_i};
  // Can we dispatch a command yet?
  // - do not commit to starting a command until we know that we can post a response when required.
  // - helps reduce the latency in responding to Target requests such as IBIs.
  wire cmd_dispatch = &{cmd_avail, cmd_start, !(cmd_attrs.wroc & rsp_desc_wfull_i),
                        // Retrying occurs only after the programmed delay has elapsed.
                        !cmd_state.available | cmd_retry_i,
                        // We must also be permitted to proceed with Command processing.
                        gstate_i == GState_Running};
  // Some command descriptors must be rejected immediately.
  wire cmd_reject   = &{cmd_avail, !cmd_init_ok, !rsp_desc_wfull_i};

  // Disable the Controller?
  wire disable_now  = (gstate_i == GState_Disabling);

  // Bus state retains information about the current mode; the Controller must switch mode and
  // speed if required when starting a new command.
  i3c_ctrl_bus_state_t bus_state;
  wire curr_ddr = (bus_state.mode == XferMode_HDRDDR) & !bus_state.i2c;

  // Start request received from one or more Targets; this can only happen in SDR mode.
  assign start_request = trx_sreq_i & !curr_ddr;

  // Direct drive request from software.
  wire direct_drive = reg2hw_i.phy_config.ctrl_direct_drive_en.q;

  // Dispatch of a subsequent command shall not happen until there is a verdict on its predecessor,
  // in case it fails.
  typedef struct packed {
    logic       pending;
    logic       dec_err;   // Error returned from command decoding?
    logic       nack_det;  // Too many NACK responses to command?
    logic       wroc;      // Write Response on Completion.
    logic       rnw;       // Read not Write.
    logic [3:0] tid;       // Transaction ID from the Command Descriptor.
  } rsp_info_t;
  rsp_info_t rsp_info;

  // Just posted in this clock cycle; allow Command processing to proceed a cycle earlier.
  logic rsp_posted;

  // First transmission of I3C Broadcast Address Header?
  //
  // - The open drain timing is more relaxed for the first I3C Broadcast address, so that I3C
  //   devices can see it even if they have spike filters enabled.
  logic i3c_first;
  // Does the current command employ the I3C Broadcast Address (7'h7e)?
  logic addr_bcst;

  // Enable Broadcast Address, in the 'Operating Context' of queued Transfer Commands (HCI 8.4.2.2).
  // - the specification does not seems to state how this should interact with `IBA_INCLUDE.` The
  //   point of this feature is to reduce the response latency to IBIs, so we play safe and use OR.
  logic pio_bcst_addr_en;
  wire use_bcst_addr = pio_bcst_addr_en | hc_control_i.iba_include.d;  // hwext, so use `d`.

  logic hj_crr_captured;

  // Transition to the next state?
  // - most of these states are waiting on the occurrence of an external event that occurs on a
  //   slower timescale than the state transitions of the FSM which operates on the main IP clock.
  // - the `proceed` signal therefore indicates whether the FSM shall advance, typically driven by:
  //   - command/response queue.
  //   - transceiver activity.
  logic proceed;
  always_comb begin
    proceed = 1'b0;
    case (state_q)
      Inactive: proceed = 1'b1;  // Transition to Idle only occurs when enabled.
      // We leave the Idle state because command(s) are pending, or because the transceiver has
      // notified us of the Start request of one or more Target(s).
      Idle:     proceed = |{direct_drive, disable_now, cmd_reject, cmd_dispatch, start_request};

      CmdBegin: proceed = 1'b1;  // DAT always available for reads.

      // We can proceed only as far as the DATCapt state before we're committed to the newly-
      // collected command, which means its predecessor must have completed.
      DATCapt:  proceed = rsp_posted | !rsp_info.pending;

      // Sending a request to the transceiver logic.
      StartSDR,
      StopSDR,
      RepStSDR,
      CmdArb,
      RepStPriv,
      CmdAddr,
      SendAckb,
      EnterDDR,
      ExitHDR,
      ReStHDR,
      CmdWord,
      TxData,
      RxData,
      TxCRC,
      RxCRC:     proceed = trx_dready_i;  // Transceiver has accepted the request.

      WaitArb,
      WaitAckb:  proceed = trx_avalid_i;  // Arbitration information available.

      // Controller Role Requests. TODO: No support for CRR presently.
      CRR:       proceed = hj_crr_captured;
      // Hot-Join Requests.
      HotJoin:   proceed = hj_crr_captured;

      // In-Band Interrupt reception.
      IBICheck:  proceed = 1'b1;
      IBIRxData: proceed = trx_dready_i;  // Request accepted.
      IBIRxWait: proceed = trx_rdvalid_i | trx_rvalid_i;  // Await data or transfer result.

      // CCC handling; remains in `CCC` until we have a verdict for this CCC segment.
      // - `ccc_proceed` means advance the internal state used when handling this CCC.
      CCC:       proceed = ccc_rsp.done & ccc_proceed;  // `done` signals command completion.

      // Command Errors; these are non-fatal errors which are posted as responses.
      CmdDecErr: proceed = 1'b1;

      // TODO: Implement this as more than a single issue; in more general use it shall be issued
      // following a RSTACT CCC Command Descriptor with TOC set.
      // - this is just for initial testing; there are various RSTACT CCC operations here.
      TargRst:   proceed = trx_dready_i;

      // Under software direct-driving of the pins we must wait until this mode is disabled.
      DirectDrv: proceed = trx_dready_i;

      // Transient states are covered here...
      // - CmdDecode, IBIDone.
      default:   proceed = 1'b1;
    endcase
  end

  always_comb begin
    // Handle only the transitions.
    // - the core logic is usually waiting on an external event.
    // - detection of the event is handled in the `proceed` logic above, the new `state_d` value
    //   is used only when `proceed` becomes asserted.
    state_d = state_q;
    case (state_q)
      // --- No activity; can disconnect and disable the Controller logic ---
      Inactive:     state_d = Idle;
      // --- Bus is idle; a command may be available but still awaiting a retry ---
      //
      // TODO: we should perform some form of access periodically in order that Targets
      // performing passive Hot-Join receive attention... Q: what, and how often, sw enable/disable?
      // We also need to report stall conditions here in the event that we're waiting for another
      // command having not received a TOC, and avoid leaving the bus in HDR-DDR mode for too long.
      Idle:         state_d = direct_drive ? DirectDrv :
                               disable_now ? Inactive  :
                                cmd_reject ? CmdDecErr :
                              cmd_dispatch ? CmdBegin  : StartSDR;

      // --- Controller Role and Hot-Join Requests ---
      CRR:          state_d = StopSDR;
      HotJoin:      state_d = StopSDR;

      // --- In-Band Interrupts ---
      IBICheck:     state_d = nacked ? StopSDR : IBIRxData;
      IBIRxData:    state_d = IBIRxWait;
      IBIRxWait:    state_d = trx_rvalid_i ? StopSDR : IBIRxData;

      // --- Command/Response handling ---
      //
      // - validate the command and read from the DAT to discover the properties of the Target.
      CmdBegin: state_d = DATCapt;
      DATCapt:  state_d = CmdDecode;
      CmdDecode: begin  // TODO: This probably wants re-expressing once the logic is finalized.
        if (cmd_dec_err) state_d = CmdDecErr;
        else begin
          // Here we need only handle the Command Descriptors that `i3c_cmd_decode` did not reject.
          case (cmd_attrs.attr)
            CmdAttr_InternalCtrl: begin
              case (cmd_intn.mipi_cmd)
                // These commands just modify the Controller internal state; no bus activity.
                MIPICmd_NoOp,
                MIPICmd_BroadAddrEnable,
                MIPICmd_EndXferHDR: state_d = Idle;
                // The Target Reset Pattern command may involve RSTACT CCC handling.
                MIPICmd_TargRstPattern:
                  case (i3c_reset_op_type_e'(cmd_intn.mipi_reserved[13:12]))
                    RstOpType_Single: state_d = TargRst;
                    default: state_d = Idle;
                  endcase
                // TODO: The following three are not yet implemented.
                MIPICmd_CtrlSDARecovery,
                MIPICmd_CtrlHandoff,
                MIPICmd_AttemptDBR: state_d = CmdDecErr;
                default: state_d = CmdDecErr;
              endcase
            end
            default: state_d = ((cmd_attrs.ddr & curr_ddr) ? CmdWord :
                                                (curr_ddr  ? ExitHDR :
                                      (cmd_state.rep_start ? CmdAddr : StartSDR)));
          endcase
        end
      end
      ExitHDR:  state_d = StopSDR;
      StartSDR: state_d = CmdArb;
      // Arbitrable Address header allows IBI, CRR and HJ requests to gain control of the I3C bus.
      CmdArb:   state_d = WaitArb;
      // The Transceiver informs us of the outcome of the Arbitrable Address Header, and we must
      // respond promptly by sending an ACK/NACK request to the transceiver logic.
      //
      // TODO: If we lose arbitration at this point we must erase any state changes that resulted
      // from starting to work on this command. We must start afresh later. More generally the
      // lifetime and (re)initialization of the members of `cmd_state` needs consideration.
      WaitArb:  state_d = trx_arb_i.arb_lost ? SendAckb : WaitAckb;
      // Repeated Start (Sr) after using the I3C Broadcast Address to command a Private Read/Write.
      RepStPriv: state_d = CmdAddr;

      // A non-arbitrable header never requires us to send ACK/NACK because there are no contenders.
      CmdAddr:  state_d = WaitAckb;

      // Awaiting Ack/Nack from the Target/Group.
      WaitAckb: state_d = trx_arb_i.nack ? StopSDR :
                        cmd_attrs.is_ccc ? CCC :
             (cmd_attrs.ddr & !curr_ddr) ? EnterDDR :
            (addr_bcst & !cmd_attrs.ddr) ? RepStPriv :  // Sr before Private Transfer, after 7'h7e.
                           cmd_attrs.rnw ? RxData : TxData;

      // Sending Ack/Nack to the Target when we lost arbitration, or did not contend.
      SendAckb: state_d = hotjoin_req ? HotJoin :
                              ibi_req ? IBICheck : CRR;
      EnterDDR: state_d = CmdWord;
      CmdWord:  state_d = cmd_attrs.rnw ? RxData : TxData;
      TxData:   state_d = data_last ? (cmd_attrs.ddr ? TxCRC : (cmd_attrs.toc ? StopSDR : RepStSDR))
                                    : TxData;
      RxData:   state_d = data_last ? (cmd_attrs.ddr ? RxCRC : (cmd_attrs.toc ? StopSDR : RepStSDR))
                                    : RxData;
      TxCRC,
      RxCRC:    state_d = cmd_attrs.toc ? ExitHDR : Idle;
      StopSDR:  state_d = Idle;
      RepStSDR: state_d = Idle;  // We need this delay to pick up _both_ command words.

      // ---- Common Command Codes ---
      //
      // The handling of Common Command Codes (CCCs) is performed according to the directions
      // of the `i3c_controller_ccc` logic. Essentially the state machine at this point is
      // following a supplied script.
      //
      // It will remain in the `CCC` state until this phase of the CCC is completed, successfully
      // or otherwise.
      CCC: begin
        case (ccc_rsp.err_status)
          ErrStatus_OK: state_d = cmd_attrs.toc ? StopSDR : RepStSDR;
          default: state_d = ErrFatal;
        endcase
      end

      // --- Command Errors ---
      CmdDecErr:  state_d = Idle;

      // --- Target Reset operations ---
      TargRst:    state_d = Idle;

      // --- Direct-driving of pins by software ---
      DirectDrv:  state_d = direct_drive ? DirectDrv : ExitHDR;

      // --- Any undefined state requires a software reset ---
      default:    state_d = ErrFatal;
    endcase
  end

  // Indicate to the controller state handling whether the Controller may be disconnected from
  // the bus; we must remain connected if there is an IBI in progress, for example.
  // - this means we've committed to entering `Inactive` and `i3c_controller_state` will deassert
  //   `enable_i` in the following cycle, leaving the FSM in `Inactive`.
  assign inactive_o = &{state_q == Idle, !direct_drive, disable_now};

  // TODO: Suspend when an error condition occurs.
  assign suspending_o = 1'b0;

  // Response to Abort request; this status indication is consulted only in `GState_Aborting`
  // so it needs no further qualification here.
  assign aborted_o = (state_q == Idle && !cmd_state.available);  // This is just temporary.
  // TODO: We do, however, need to respond more promptly to `Aborting` in a few states such as
  // part-way through handling an Address Assignment command. HCI 6.5.6 seems to indicate that
  //` transfer_aborted_o` shall be asserted only when actually reporting `HC_ABORTED` in one or
  // more Response Descriptors. Also, note that there are _two_ abort mechanisms(!); HC_CONTROL and
  // PIO_CONTROL.
  assign transfer_aborted_o = (gstate_i == GState_Aborting) & aborted_o;

  // Destination of received data.
  typedef enum logic [0:0] {
    RxDest_Buf,  // Rx Data Buffer (e.g Private Read Transfer).
    RxDest_IBI   // IBI Data Buffer.
  } rx_dest_e;

  rx_dest_e rx_dest;
  // This is a simple combinational value for now, but it may need to become stored state.
  assign rx_dest = (state_q inside {IBIRxData, IBIRxWait}) ? RxDest_IBI : RxDest_Buf;

  // Not every command processed requires a read from the DAT, and additionally some of the DAT
  // reads are performed by the DAT cache rather than the FSM itself.
  logic datf_re;
  logic datf_re_q;

  // Command/Transfer handling.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q           <= Inactive;
      i3c_first         <= 1'b1;
      trans_type        <= TransType_None;
      cmd_state         <= 'b0;
      datf_re_q         <= 1'b0;
      dat_entry         <= 'b0;
      data_len          <= 'b0;
      txd_imm           <= 1'b0;
      bus_state.mode    <= XferMode_SDR0;
      bus_state.i2c     <= 1'b0;
      cmdq_lo_valid     <= 1'b0;
      cmdq_lo_data      <= '0;
      pio_bcst_addr_en  <= 1'b0;
    end else if (sw_reset_i) begin
      state_q             <= Inactive;
      i3c_first           <= 1'b1;
      trans_type          <= TransType_None;
      bus_state.mode      <= XferMode_SDR0;
      bus_state.i2c       <= 1'b0;
      cmdq_lo_valid       <= 1'b0;
      cmd_state.available <= 1'b0;
      cmd_state.started   <= 1'b0;
      pio_bcst_addr_en    <= 1'b0;
      cmd_state.rst_csect <= 1'b0;
    end else if (enable_i) begin
      if (proceed) begin  // The progress of the state machine is conditional.
        case (state_q)
          // Proceeding from Idle state to CmdBegin means we have a command available to be
          // processed, even if we are merely rejecting it with an error.
          Idle: begin
            // Did we initiate this transfer?
            cmd_state.available <= cmd_dispatch;
            trans_type          <= cmd_dispatch ? TransType_Cmd : TransType_Intr;
          end
          // Capture the DAT entry (read data from DAT could be altered by software access);
          // - note that we also wait here until the result from the previous command has been
          //   posted into the Response Queue.
          DATCapt: if (datf_re_q) dat_entry <= dat_rdata_i;
          // Now that we have the captured DAT entry available to complete the command decoding,
          // we can proceed
          CmdDecode: begin
            if (!cmd_state.started) begin
              cmd_state.dev_index <= cmd_attrs.dev_index;
              cmd_state.reps_left <= cmd_attrs.reps_left;
              cmd_state.retry_cnt <= cmd_attrs.retry_cnt;
            end
            cmd_state.started <= 1'b1;
            // Deferring the `data_len` initialization until this state, where we wait until any
            // earlier response has been posted, means that the response-handling logic can just use
            // `data_len` directly.
            data_len <= cmd_attrs.data_len;
            if (cmd_attrs.attr == CmdAttr_InternalCtrl) begin
              case (cmd_intn.mipi_cmd)
                MIPICmd_BroadAddrEnable: pio_bcst_addr_en <= cmd_intn.mipi_reserved[12];
                MIPICmd_TargRstPattern:
                  case (i3c_reset_op_type_e '(cmd_intn.mipi_reserved[13:12]))
                    RstOpType_RSTACT: cmd_state.rst_csect <= 1'b1;
                    default:          cmd_state.rst_csect <= 1'b0;
                  endcase
                default: begin end
              endcase
            end
            // The first - and only - word of TxD may come from the Command Descriptor itself.
            txd_imm <= &{cmd_attrs.attr == CmdAttr_ImmTransfer, |cmd_imm.dtt, cmd_imm.dtt != 3'h5};
          end
          // When we've learned the outcome of any arbitration, the transfer type may need updating.
          WaitArb: if (trx_arb_i.arb_lost) begin
            trans_type <= TransType_Intr;
            // We need to reset `available` in order to retry it as soon as possible, but we do not
            // modify `started` or `retry_count` because that would erase the past history of this
            // command.
            cmd_state.available <= 1'b0;
            // Set the data length to the maximum value so that we keep issuing SDR read requests
            // and we do not artificially limit the maximum length of the IBI payload.
            data_len <= 16'hffff;
          end
          // Arbitration was won in the Arbitrable Address Header signaling; collect ACK/NACK
          // response from the Target/Group.
          WaitAckb: begin
            // Once we've successfully issued the first I3C Broadcast Address we can transmit
            // faster.
            if (addr_bcst & ~trx_arb_i.arb_lost) i3c_first <= 1'b0;
          end
          // Track changes to the current bus mode.
          EnterDDR: begin
            bus_state.mode <= cmd_attrs.mode;
            bus_state.i2c  <= cmd_attrs.i2c;
          end
          ExitHDR: begin
            bus_state.mode <= XferMode_SDR0;
            bus_state.i2c  <= 1'b0;
          end
          // Count the transferred bytes.
          TxData, RxData: begin
            data_len  <= next_len;
            txd_imm   <= 1'b0;
          end
          // Track when we've generated a Repeated Start (Sr).
          // - used within CCC transfers to decide whether we're targeting a specific address.
          // - used with Private Transfers that have been commenced using the I3C Broadcast Address.
          RepStPriv,
          RepStSDR: cmd_state.rep_start <= 1'b1;
          StopSDR: begin
            // Commands may be retried a programmable number of times; note that we may have
            // responded to a request from a Target between retries of a command that has previously
            // been NACKed, hence the qualification with `trans_type`.
            if ((trans_type == TransType_Cmd) & nacked) begin
              cmd_state.retry_cnt <= cmd_state.retry_cnt - |cmd_state.retry_cnt;
            end
            cmd_state.rep_start <= 1'b0;
          end
          default: begin end
        endcase
        state_q <= state_d;
      end else begin
        // Not leaving the current state, but some activity is still occurring...
        case (state_q)
          CCC: begin
            if (ccc_rsp.txd_consume) begin
              data_len  <= next_len;
              txd_imm   <= 1'b0;
            end
          end
          default: begin end
        endcase
      end

      // Only read from the Command Queue when command processing is enabled.
      if (cmd_enabled & cmd_desc_rvalid_i) begin
        // Capture the first DWORD of the queued command.
        if (!cmdq_lo_valid)    cmdq_lo_data   <= cmd_desc_rdata_i;
        if (cmd_desc_rready_o) cmdq_lo_valid  <= !cmdq_lo_valid;
        // When completing and dropping a command we must invalidate `cmd_state` to ensure there is
        // no persistent state from this command.
        if (cmd_complete) begin
          cmd_state.available <= 1'b0;
          cmd_state.started   <= 1'b0;
          trans_type          <= TransType_None;
        end
      end

      // Remember whether a DAT read was performed.
      datf_re_q <= datf_re;
    end
  end

  // State index within the CCC handling FSM state.
  // - no need for software reset handling; the FSM will reset on entering `StartSDR`.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) ccc_idx <= '0;
    else if (enable_i) begin
      case (state_q)
        // Potentially entering CCC handling. Index will be unused if not, but we _must_ initialize
        // this for the start of every CCC operation, no matter how any previous operation
        // concluded.
        StartSDR: ccc_idx <= '0;
        // FSM remains in CCC handling until instructed to finish.
        CCC: if ((ccc_rsp.rst_idx | ccc_rsp.inc_idx) & ccc_proceed) begin
            ccc_idx <= (ccc_rsp.rst_idx ? 4'h0 : ccc_idx) + 4'(ccc_rsp.inc_idx);
          end
        default: begin end
      endcase
    end
  end

  // Updating of CCC register state.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int unsigned r = 0; r < CtrlCR_Count; r++)
        reg_state[r] <= '0;
    end else if (enable_i) begin
      // Capture/Reset the CCC and DEFB attributes when starting a command.
      // TODO: invalidate state when a cmd is rejected.
      if (state_q == CmdBegin) begin
        reg_state[CtrlCR_CCC]   <= cmd_attrs.ccc;
        // Similarly for the DEFB.
        reg_state[CtrlCR_DEFB]  <= cmd_attrs.defb;
        // Update the CCC/DEFB validity indicator.
        reg_state[CtrlCR_Status][CtrlStat_HasDEFB]     <= cmd_attrs.has_defb;
        reg_state[CtrlCR_Status][CtrlStat_SendFraming] <= ccc_framing_reqd;
      end else if (state_q == StopSDR) begin
        reg_state[CtrlCR_Status] <= 8'b0;
      end
      // Perform register writes from the CCC handling.
      if (ccc_rsp.reg_we) reg_state[ccc_rsp.reg_widx] <= ccc_rsp.reg_wdata;
    end
  end

  // Command completion states.
  wire cmd_sdr_done = state_q inside {StopSDR, RepStSDR};
  wire cmd_ddr_done = state_q inside {RxCRC, TxCRC};
  // - Completion does _not_ imply success, only that the Command Descriptor can be discarded and an
  //   outcome may be posted.
  wire cmd_trans_done = &{cmd_sdr_done | cmd_ddr_done,
                        ~|cmd_state.retry_cnt || !nacked,  // Retries in response to Nack.
                        ~|cmd_state.reps_left, proceed};   // Iteration within Address Assignment.
  // - Any transfer such as an IBI request that does involve a Command Descriptor shall be excluded.
  assign cmd_complete = (trans_type == TransType_Cmd) &
                       |{cmd_trans_done,
                        (state_q == TargRst) & proceed,  // Target Reset internal command.
                        (state_q == CmdDecErr)};         // Command rejected.

  // Reading of commands; we use the FIFO output directly for the upper half of the Command
  // Descriptor, so it is consumed upon completion of the command.
  assign cmd_desc_rready_o = !cmdq_lo_valid || cmd_complete;

  // Retrying of commands that received a NACK.
  // - the I3C Basic specification describes a single retry for Direct GET CCCs (4.3.7.2.3) but it
  //   does not stipulate the time interval before retrying.
  // - the HCI specification permits up to 3 retries on a per-Target basis (section 8.1) for Private
  //   Read/Write transfers.
  // - we use the same interval timer for both cases, but don't start the timer if we're giving up.
  assign cmd_nacked_o = &{state_q == WaitAckb, trx_avalid_i, trx_arb_i.nack, |cmd_state.retry_cnt};

  // Report an excess NACK count for an attempted Command transfer.
  assign cmd_nack_excess = &{trans_type == TransType_Cmd, cmd_trans_done, nacked};

  // Reading of data from the Tx buffer.
  // TODO: Availability check required....must abort transfer if buffer underruns.
  assign txbuf_rready_o = &{cmd_attrs.attr != CmdAttr_ImmTransfer, state_q == TxData, trx_dready_i}
                        | &{state_q == CCC, ccc_rsp.txd_consume, !txd_imm};

  // Reverse the order of the bytes within the supplied data word.
  function automatic logic [DataWidth-1:0] revb(logic [DataWidth-1:0] wdata);
    for (int unsigned ib = 0; ib < DataWidth; ib += 8) begin
      revb[DataWidth - ib - 8 +: 8] = wdata[ib +: 8];
    end
  endfunction

  // Reverse the order of the half-words (16 bits) within the supplied data word.
  function automatic logic [DataWidth-1:0] revh(logic [DataWidth-1:0] wdata,
                                                logic      [Log2DW:0] bits_left);
    // We may need to pad the final half-word with a 0 byte; half-words are transmitted as
    // big endian, though, so the final (non-existent) byte is bits [7:0] of the half-word.
    for (int unsigned ib = 0; ib < DataWidth; ib += 16) begin
      // Data Words transmit the first byte within the MSBs.
      revh[DataWidth - ib - 16 +: 16] = {wdata[ib +: 8],
                                         wdata[ib + 8 +: 8] & {8{ib + 8 < bits_left}}};
    end
  endfunction

  // Tx data does not need decomposing into smaller requests, but it does need twizzling.
  // - HDR-DDR data is sent as 16-bit quantities, with the least significant part of the DWORD
  //   sent first, and we need to introduce zeros for any final padding byte.
  // - SDR data is sent as 8-bit quantities with the LSB going first, so this is a simple byte swap.
  logic [DataWidth-1:0] tx_data_pre;
  always_comb begin : gen_tx_data
    // The data for transmission may come from the Command Descriptor itself if short enough.
    tx_data_pre = txd_imm ? {cmd_imm.data_byte_4,
                             cmd_attrs.has_defb ? cmd_imm.data_byte_4 : cmd_imm.data_byte_3,
                             cmd_attrs.has_defb ? cmd_imm.data_byte_3 : cmd_imm.data_byte_2,
                             cmd_attrs.has_defb ? cmd_imm.data_byte_2 : cmd_imm.data_byte_1}
                          : txbuf_rdata_i;  // Usual case.

    // Move the 8- or 16-bit units into the correct order for transmission by the Transceiver.
    // - MSB is driven onto the I3C bus first.
    // - CCC logic shall expect the data in the same format as the Transceiver.
    if (cmd_attrs.ddr) begin : ddr_data
      bit [Log2DW-3:0] bytes_left;
      // Calculate the number of bytes remaining, since we may need to pad with a zero byte.
      bytes_left = data_last ? data_len[2:0] : 3'b100;
      tx_data = revh(tx_data_pre, {bytes_left, 3'b0});
    end else tx_data = revb(tx_data_pre);
  end

  // Address Assignment Commands perform multiple DAT reads, incrementing the DAT index with each
  // command decode, so it is pre-decremented. We therefore suppress a read before the first Sr.
  wire datf_assign_re = (cmd_attrs.attr == CmdAttr_AddrAssignment) & cmd_state.rep_start;
  // DAT reads are also required, but only for typical non-Broadcast Transfer Commands.
  // - Broadcast CCCs do not require a DAT read.
  // - Internal Control Commands do not require DAT access.
  assign datf_re = (state_q == CmdBegin) & proceed & (!cmd_attrs.brd_ccc | datf_assign_re);

  // Reads from the Device Address Table (DAT) occur for most Commands, but may also occur in
  // response to In-Band Interrupt and Controller-Role Requests.
  // - since all of these are mediated by the FSM there is no need to worry about collisions.
  logic [DATAddrW-1:0] datc_idx;
  wire datc_re;
  assign dat_re_o  = datf_re | datc_re;  // Two sources: FSM and Cache.
  assign dat_idx_o = datc_re ? datc_idx : cmd_attrs.dev_index;

  // Writes to the Device Characteristics Table (DCT) occur only during ENTDAA processing.
  // - since the DCT TABLE_INDEX field must be `hwext` it is implemented here.
  logic                dct_rewind;  // Rewind to the start of the current DCT entry?
  logic                dct_commit;  // Commit this DCT entry by advancing the index?
  logic                dct_wupper;  // Upper half of DCT entry to be written next?
  logic [DCTAddrW-1:0] dct_idx;
  // Wraparound of the DCT TABLE_INDEX may occur but the Driver software must handle that.
  wire  [DCTAddrW-1:0] dct_idx_next = dct_idx + 'b1;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dct_idx     <= 'b0;
      dct_wupper  <= 'b0;
    end else if (sw_reset_i) begin
      dct_idx     <= 'b0;  // Must reset this because it is software-visible in the HCI registers.
      dct_wupper  <= 1'b0;
    end else begin
      // The DCT index may be incremented by hardware or written by software.
      // - comparison here handles non-2^n entries.
      // - not gated with `enable_i` because software accesses the `dct_idx` register field and
      //   could do so whilst the Controller is not enabled.
      if (dct_commit) dct_idx <= (dct_idx_next >= NumDCTEntries) ? 'b0 : dct_idx_next;
      else if (dct_idx_qe_i) dct_idx <= dct_idx_q_i;  // Initialization by software.
      // It takes two write operations from the hardware to complete a DCT entry.
      if (|{dct_we_o, dct_commit, dct_rewind}) begin
        dct_wupper <= ~|{dct_wupper | dct_commit | dct_rewind};
      end
    end
  end
  // Current index into the Device Characteristics Table.
  assign dct_idx_o = dct_idx;

  // ---------------------------------- Request generation -----------------------------------------

  // Generate request to the transceiver logic; this is a purely combinational module that
  // constructs the request from the current FSM state and the data to be transferred.
  i3c_ctrl_req_gen #(
    .ClkFreq  (ClkFreq),
    .DataWidth(DataWidth)
  ) u_req_gen (
    // Configuration.
    .reg2hw_i       (reg2hw_i),
    .use_bcst_addr_i(use_bcst_addr),

    // The current FSM state.
    .state_i        (state_q),

    // Information about the current Command Descriptor and transfer.
    .trans_type_i   (trans_type),
    .cmd_state_i    (cmd_state),
    .cmd_attrs_i    (cmd_attrs),
    .dat_entry_i    (dat_entry),
    // Additional state-specific information.
    .i3c_first_i    (i3c_first),
    .send_nack_i    (nacked),
    .xfer_mode_i    (ibi_xfer_mode),

    // Data transmission.
    .tx_data_i      (tx_data),
    .data_last_i    (data_last),
    .dlen_i         (dlen),

    // Response from the CCC handling logic.
    .ccc_rsp_i      (ccc_rsp),

    // Timing parameters; target- and transfer-invariant.
    .tcas_d2_o      (tcas_d2_o),
    .tcbp_d2_o      (tcbp_d2_o),

    // Using I3C Broadcast Address?
    .addr_bcst_o    (addr_bcst),
    // Request to the transceiver logic.
    .trx_dvalid_o   (trx_dvalid_o),
    .trx_dreq_o     (trx_dreq_o)
  );

  // ----------------------------------- Common Command Codes --------------------------------------

  // Controller-side Common Command Code handling.
  i3c_controller_ccc #(
    .DataWidth  (DataWidth)
  ) u_ctrl_ccc (
    // CCC handling enabled and active?
    .enable_i   (enable_i & (state_q == CCC)),

    // Configuration.
    .reg2hw_i   (reg2hw_i),

    // Register state, including the CCC itself.
    .r_i        (reg_state),

    // Current command state, for any additional information required.
    .cmd_state_i(cmd_state),

    // Requests from the Controller FSM.
    .ccc_req_i  (ccc_req),

    // Responses to the Controller FSM.
    .ccc_rsp_o  (ccc_rsp)
  );

  // -------------------------------------- Data reception -----------------------------------------

  logic rxbuf_wdata_accepted, ibi_data_accepted;
  logic rx_wvalid_q;
  logic [DataWidth-1:0] rx_data_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rx_data_len <= '0;
      rx_wvalid_q <= 1'b0;
      rx_data_q   <= '0;
    end else if (sw_reset_i) rx_wvalid_q <= 1'b0;
    else if (enable_i) begin
      // TODO: Is this check sufficient/appropriate?
      if ((state_q == DATCapt) & !rsp_info.pending) begin
        rx_data_len <= '0;
      end else begin
        // TODO: Consider more carefully the use of `cmd_state` here.
        case ({cmd_state.available, cmd_attrs.attr})
          {1'b1, CmdAttr_AddrAssignment}: begin
            // The `data_length` field of the posted response indicates only whether there _may_ be
            // other devices in need of a dynamic address. Zero indicates that the command did not
            // manage to assign all `dev_count` addresses (HCI 8.4.1.1).
            rx_data_len   <= {15'b0, ~|cmd_state.reps_left};
          end
          default: begin
            if (trx_rdvalid_i | rx_wvalid_q) begin
              // Read data is steered to either the Rx Buffer or the IBI Data Buffer.
              rx_wvalid_q <= (trx_rdvalid_i | rx_wvalid_q) &
                            ~(rxbuf_wdata_accepted | ibi_data_accepted);
            end
            if (trx_rdvalid_i & ~rx_wvalid_q) begin
              // Keep old data rather than accept new, to avoid corrupting the transmitted data;
              // TODO: this shall be reported as an error condition.
              rx_data_len <= rx_next_len;
              rx_data_q   <= rx_data;
            end
          end
        endcase
      end
    end
  end

  // Writing into the DCT of Target properties that were read during Dynamic Address Assignment.
  // - writing may proceed safely even though we have not yet received and validated all data;
  //   committing the entry (advancing the index) shall occur only once the command has succeeded.
  assign dct_commit  = dct_we_o & dct_wupper;
  // Rewind to the start of the current DCT entry, ready for handling a new Target during ENTDAA.
  assign dct_rewind  = state_q inside {CmdArb, CmdAddr};
  assign dct_we_o    = (cmd_attrs.attr == CmdAttr_AddrAssignment) & trx_rdvalid_i;
  assign dct_wmask_o = dct_wupper ? 9'h1f0 : 9'h00f;
  always_comb begin
    dct_wdata_o.pid_hi = trx_rdata_i.rdata;
    dct_wdata_o.bcr    = trx_rdata_i.rdata[15:8];
    dct_wdata_o.dcr    = trx_rdata_i.rdata[7:0];
    dct_wdata_o.pid_lo = trx_rdata_i.rdata[31:16];
    // The HCI specification says that the `DYNAMIC_ADDRESS` field (HCI 8.2) includes the parity
    // bit but it does not specify its location. The MIPI Alliance driver does not use this
    // field, and we're supposing it has the same format as the corresponding DAT field, rather
    // than the transmission bit order within the ENTDAA operation.
    // TODO: Is there a way to resolve this so that driver software need not be adapted?
    dct_wdata_o.dynamic_address = {dat_entry.dynamic_address[23],      // Parity bit
                                   dat_entry.dynamic_address[22:16]};  // Dynamic address
  end

  // Conversion of read data from I3C transmission order to Little Endian DWORDs.
  always_comb begin
    rx_data = '0;
    if (trx_rdata_i.ddr) begin
      // Data Words carry the first byte in the MSBs. The LSBs may be unused for the final word.
      rx_data = {(rx_len > 'h2) ? {trx_rdata_i.rdata[7:0],   trx_rdata_i.rdata[15:8]}  : 16'b0,
                 (rx_len > 'h2) ? {trx_rdata_i.rdata[23:16], trx_rdata_i.rdata[31:24]}
                                : {trx_rdata_i.rdata[7:0],   trx_rdata_i.rdata[15:8]}};
    end else begin
      // Bytes were shifted into the buffer from the LSB, left-shifting, so the first byte
      // received (which should be in the LSB of the output word) will be in the highest used
      // bits presently; exactly where depends upon the number of bytes received.
      case (rx_len[1:0])
        2'b00:   rx_data = {trx_rdata_i.rdata[7:0],   trx_rdata_i.rdata[15:8],
                            trx_rdata_i.rdata[23:16], trx_rdata_i.rdata[31:24]};
        2'b01:   rx_data = {24'b0, trx_rdata_i.rdata[7:0]};
        2'b10:   rx_data = {16'b0, trx_rdata_i.rdata[7:0], trx_rdata_i.rdata[15:8]};
        default: rx_data = {8'b0,  trx_rdata_i.rdata[7:0], trx_rdata_i.rdata[15:8],
                                   trx_rdata_i.rdata[23:16]};
      endcase
    end
  end

  // -------------------------------- Steering of Read Data ----------------------------------------
  //
  // Note: the write strobe remains asserted until the data is accepted; the shared message buffer
  // cannot always accept write data immediately even if there is space available for the data.

  // Write the data into the Rx Buffer.
  assign rxbuf_wvalid_o = (rx_dest == RxDest_Buf) & (rx_wvalid_q | trx_rdvalid_i);
  assign rxbuf_wdata_o  = trx_rdvalid_i ? rx_data : rx_data_q;
  assign rxbuf_wdata_accepted = rxbuf_wvalid_o & rxbuf_wready_i;

  // We also need to support writing into the IBI data buffer.
  assign ibi_data_wvalid_o = (rx_dest == RxDest_IBI) & (rx_wvalid_q | trx_rdvalid_i);
  assign ibi_data_wdata_o  = trx_rdvalid_i ? rx_data : rx_data_q;
  assign ibi_data_accepted = ibi_data_wvalid_o & ibi_data_wready_i;

  // ------------------------------------ Response construction ------------------------------------

  // Response to Driver.
  i3c_xfer_rsp_t rsp;
  logic rsp_write_q;
  assign rsp_desc_wvalid_o = rsp_write_q;
  assign rsp_desc_wdata_o  = rsp;

  // Final response for this transfer received from the transceiver?
  // - this response indicates the success/failure of the transfer, including any error information.
  // - do not create a response for an IBI payload read.
  wire rsp_received = (rx_dest != RxDest_IBI) & trx_rvalid_i;
  wire rsp_success = (trx_rsp_i.err_status == ErrStatus_OK);
  wire rsp_post = rsp_info.pending & |{rsp_received & rsp_info.wroc,  // From transceiver.
                                       rsp_received & !rsp_success,   // All errors are posted.
                                       rsp_info.dec_err,              // From command decode.
                                       rsp_info.nack_det};            // From command execution.
  wire rsp_drop = &{rsp_info.pending, rsp_received, !rsp_info.wroc, rsp_success};

  assign rsp_posted = rsp_desc_wvalid_o & rsp_desc_wready_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rsp_write_q <= 1'b0;
      rsp         <= '0;
    end else if (sw_reset_i) rsp_write_q <= 1'b0;
    else if (enable_i) begin
      rsp_write_q <= (rsp_post | rsp_write_q) & ~rsp_desc_wready_i;
      if (rsp_post) begin
        rsp.err_status  <= rsp_info.dec_err  ? ErrStatus_NotSupported :
                           rsp_info.nack_det ? ErrStatus_NACK : trx_rsp_i.err_status;
        rsp.tid         <= rsp_info.tid;
        rsp.reserved    <= 'b0;  // Not used; pacify synthesis.
        // TODO: The reported `DATA_LENGTH` field can be incorrect for early-terminated writes.
        rsp.data_length <= (rsp_info.nack_det | ~rsp_info.rnw) ? data_len :  // From the command.
                                                 trx_rdvalid_i ? rx_next_len : rx_data_len;
      end
    end
  end

  // Construction of the next response to post.
  rsp_info_t rsp_next;
  always_comb begin : gen_rsp_next
    logic cmd_acked, dec_err;
    logic bcst_priv;

    // A new response cannot coincide with the posting or dropping of the previous one because
    // the FSM waits in `DATCapt` until that the previous response has been handled.
    rsp_next = rsp_info;
    if (rsp_posted | rsp_drop) rsp_next.pending = 1'b0;

    dec_err = &{state_q == Idle, !direct_drive, !disable_now, cmd_reject} | (state_q == CmdDecErr);
    cmd_acked = &{state_q == WaitAckb, trx_avalid_i, !trx_arb_i.nack};
    // Is this acknowledgement for the Arbitrable I3C Broadcast Address of a Private SDR transfer?
    bcst_priv = &{addr_bcst, ~cmd_attrs.is_ccc, ~cmd_attrs.ddr};

    if (|{cmd_acked & ~bcst_priv, dec_err, cmd_nack_excess}) begin
      rsp_next.pending  = 1'b1;
      rsp_next.dec_err  = dec_err;
      rsp_next.nack_det = cmd_nack_excess;
      // Write Response On Completion; Response Status required?
      // - responses are optional only for successful write transfers.
      rsp_next.wroc     = cmd_attrs.wroc | cmd_attrs.rnw;
      rsp_next.rnw      = cmd_attrs.rnw;  // Read not Write transfer.
      rsp_next.tid      = cmd_attrs.tid;  // Transaction ID from the Command Descriptor.
    end
  end

  // The transceiver always posts a response to us, so that we know that we can safely proceed
  // to the next command. The `wroc` (Write Response on Completion) field indicates whether we are
  // required to post to the Response Queue.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) rsp_info <= '0;  // Clears `pending`.
    else if (enable_i) rsp_info <= rsp_next;
  end

  // TODO: Presently always able to receive a response; this indication is important in permitting
  // the transceiver to proceed after reporting an error condition.
  assign trx_rready_o = 1'b1;

  // ------------------------------------- In-Band Interrupts --------------------------------------

  // Writing into the IBI Status Descriptor FIFO or IBI Data Queue.
  // - together these form the IBI_PORT of the HCI.
  wire  ibi_init  = (state_q == WaitArb);  // Initialize the IBI segment tracking.
  wire  ibi_write = (state_q == IBIRxWait) & trx_rdvalid_i;  // Single cycle assertion.
  wire  ibi_rlast = trx_rdata_i.rlast;  // Have we received the final byte of the IBI Payload?
  logic ibi_segmax;  // Does the current write terminate the IBI Data Segment?
  logic arb_nack;

  // Software may request notification when an IBI, CRR or HJ is rejected by the Controller.
  logic ibi_capt_crr_hj;
  always_comb begin
    case (state_q)
      // Hot-Join and CRR carry no data bytes and are transient states.
      HotJoin:  ibi_capt_crr_hj = reg2hw_i.ibi_notify_ctrl.notify_hj_rejected.q  | !nacked;
      CRR:      ibi_capt_crr_hj = reg2hw_i.ibi_notify_ctrl.notify_crr_rejected.q | !nacked;
      // IBI (usually) carries a data payload and an ACKed IBI writes the status descriptor later.
      // TODO: Some IBIs, as indicated by BCR[2], but we don't have that information!
      IBICheck: ibi_capt_crr_hj = reg2hw_i.ibi_notify_ctrl.notify_ibi_rejected.q;
      default:  ibi_capt_crr_hj = 1'b0;
    endcase
  end

  // TODO: We need to wend the Broadcast CCCs into the IBI logic, when Standby Controller operation
  // is supported.
  assign stby_bcst_wready_o = 1'b1;
  // Proposed IBI Status Descriptor.
  i3c_ibi_status_t ibi_stat_desc;
  i3c_ibi_status_e ibi_status_type;
  assign ibi_status_type = IBIStatus_Regular;  // The only type presently supported.

  // Construction of IBI Status Descriptor during IBI reception.
  always_comb begin
    // Zeroes the `reserved` field, `ts` (No timestamp information) and `chunks` (DMA Mode only).
    ibi_stat_desc = '0;
    ibi_stat_desc.status_type = ibi_status_type;
    // Address and RnW indication from the IBI, CRR or HJ request.
    // - the least significant bit indicates `1` for a real IBI, `0` for CRR or HJ request.
    ibi_stat_desc.ibi_id = {trx_arb_i.addr, trx_arb_i.ibi};
    case (ibi_status_type)
      // This applies to IBI, CRR and HJ, as well as any rejection of such for which notification
      // has been requested via `IBI_NOTIFY_CTRL`.
      IBIStatus_Regular: begin
        // Hot-Join requests do not consult the DAT cache and cannot be rejected.
        ibi_stat_desc.ibi_sts     = nacked;
        // CRR and Hot-Join requests shall always return 1'b0 for these two fields (HCI 8.6.3).
        ibi_stat_desc.error       = (trx_rsp_i.err_status != ErrStatus_OK) & ~ibi_capt_crr_hj;
        ibi_stat_desc.last_status = ibi_rlast & ~ibi_capt_crr_hj;
      end
      // Notes: IBIStatus_StbyCrBastCCC required when Controller Role Handoff is implemented.
      // - IBI Credit Counter, Scheduled Command Execution Reports and Auto-Command Read Data are
      //   presently not implemented.
      default: begin end
    endcase
  end

  // To maintain consistent IBI state, the logic must be reset if either of the constituent FIFOs
  // is reset.
  wire ibi_sw_reset = |{sw_reset_i, fifo_rst_i[FIFO_IBIQ], fifo_rst_i[FIFO_IBIStD]};

  // Modified descriptor, with DATA_LENGTH completed appropriately.
  i3c_ibi_status_t mod_stat_desc;

  // Controller-side tracking of In-Band Interrupt Status Descriptors.
  //
  // - alongside the IBI Data Buffer there is also a queue of IBI Status Descriptors.
  // - the status descriptors are conveyed through a separate logical FIFO in the message buffer
  //   because they can only be created after the described data has been written into the buffer.
  // - on the HCI/Driver side, a single logical port reads from the appropriate FIFO, interleaving
  //   the status descriptors and the described data DWORDs.
  // - as of HCI v1.2 the IBI queue also carries notifications of other events, not just IBIs.
  i3c_controller_ibi #(.Log2DBW(Log2DBW)) u_ibi (
    // Clock and reset.
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),

    .enable_i         (enable_stby_i),

    // Software reset to the FIFO.
    .sw_reset_i       (ibi_sw_reset),

    // Configuration.
    .ibi_status_size_i(reg2hw_i.ibi_config.size_val.q),
    .data_seg_size_i  (reg2hw_i.queue_thld_ctrl.ibi_data_segment_size.q),

    // Indication of whether the current write terminates an IBI Data Segment.
    .last_o           (ibi_segmax),

    // Writes into the IBI Status Descriptor FIFO and IBI Data Queue.
    .init_i           (ibi_init),
    .write_i          (ibi_write),
    .wlen_i           (rx_len),
    .wstat_desc_i     (ibi_stat_desc),

    // Modified IBI Status Descriptor to be written into the FIFO.
    .stat_desc_o      (mod_stat_desc)
  );

  // IBI Status Descriptor written into the queue?
  wire ibi_stat_accepted = ibi_stat_wvalid_o & ibi_stat_wready_i;

  // Response available to IBI Payload collection?
  wire ibi_response = (state_q == IBIRxWait) & trx_rvalid_i;  // Single-cycle assertion.

  // Capturing an IBI Status Descriptor?
  // - if capturing is the result of the IBI Data Segment reaching its maximum permissible length,
  //   we do not yet know how to complete its fields; committing must be deferred.
  // - CRR and Hot-Join requests have no data and are captured and committed without delay.
  wire ibi_stat_capture = |{(ibi_write & (ibi_segmax | ibi_rlast)), ibi_response, ibi_capt_crr_hj};
  i3c_ibi_status_t ibi_stat_desc_q;
  logic ibi_stat_captured_q;
  logic ibi_stat_wvalid_q;
  assign hj_crr_captured = ibi_stat_captured_q;

  // Commit to writing an IBI Status Descriptor now that its contents are known; in particular we
  // know how `LAST_STATUS`, `ERROR` and `IBI_STS` should be populated.
  wire ibi_stat_commit = (ibi_stat_captured_q & (trx_rdvalid_i | ibi_capt_crr_hj)) | ibi_response;
  wire ibi_stat_last = trx_rvalid_i;

  // Capture the IBI Status Descriptor.
  //
  // Should we NACK an IBI request if there is no slot available for a status descriptor?
  // TODO: Check the semantics of IBI NACK. Normally the Controller is required to send `DISEC`
  // afterwards which means that retrying will not occur, so perhaps it's a bit heavy-handed.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ibi_stat_captured_q <= 1'b0;
      ibi_stat_wvalid_q   <= 1'b0;
      ibi_stat_desc_q     <= '0;
    end else if (ibi_sw_reset) begin
      ibi_stat_captured_q <= 1'b0;
      ibi_stat_wvalid_q   <= 1'b0;
    end else if (enable_stby_i) begin
      if (ibi_stat_commit & !ibi_stat_wfull_i) begin
        ibi_stat_wvalid_q <= 1'b1;
      end else if (ibi_stat_accepted) begin
        ibi_stat_wvalid_q <= 1'b0;
      end
      if (ibi_stat_capture) begin
        ibi_stat_captured_q <= 1'b1;
        ibi_stat_desc_q     <= mod_stat_desc;
      end else if (ibi_stat_commit) begin
        ibi_stat_captured_q <= 1'b0;
        ibi_stat_desc_q.last_status <= ibi_stat_last;
      end
    end
  end
  assign ibi_stat_wvalid_o = ibi_stat_wvalid_q;
  assign ibi_stat_wdata_o  = ibi_stat_desc_q;

  // TODO: We should also report data loss somehow.
  // wire ibi_stat_loss = ;
  // wire ibi_data_loss = ;

  // ----------------------------------------- DAT Cache -------------------------------------------

  // DAT cache searching.
  // - searches are performed in response to IBI/CRR requests and in the processing of Controller
  //   Role Handoff commands.
  logic       datc_req, datc_gnt;
  logic [6:0] datc_addr;
  // TODO: CRR Handoff MIPI internal comand needs DAT Cache access too.
  assign datc_req  = &{state_q == WaitArb, trx_avalid_i, trx_arb_i.arb_lost};
  assign datc_addr = datc_req ? trx_arb_i.addr : cmd_intn.mipi_reserved[18:12];

  // Arbitration verdict, when DAT Cache is used for IBI/CRR lookups.
  // - since the DAT may not describe all devices we opt (in `i3c_dat_cache`) to reject IBI/CRR
  //   requests for a device not described, and for IBI issue a `DISEC`. This avoids us wasting
  //   bus bandwidth and perhaps makes us a bit more resilient.
  //   TODO: We need to issue `DISEC`, and we may want to make the default verdict configurable.
  // - the software driver can always be informed of the rejection via `IBI_NOTIFY_CTRL`.
  logic datc_hit;
  assign trx_aready_o = trx_avalid_i & (datc_gnt | ~trx_arb_i.arb_lost);
  assign arb_nack = ibi_req ? ibi_reject :
                cr_role_req ? crr_reject : reg2hw_i.hc_control.hot_join_ctrl.q;

  i3c_dat_cache #(
    .NumDATEntries  (NumDATEntries),  // Number of entries in the DAT.
    .CacheSize      (DATCacheSize)    // Maximum number of cached entries.
  ) u_dat_cache(
    // Clock and reset.
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // Control inputs.
    .enable_i     (enable_i),
    .sw_reset_i   (sw_reset_i),

    // Driver updates to cache entries.
    .we_i         (sw_datc_we_i),
    .widx_i       (sw_datc_widx_i),
    .wdata_i      (sw_datc_wdata_i),

    // Read access.
    .re_i         (datc_req),
    .rgnt_o       (datc_gnt),
    .raddr_i      (datc_addr),
    .rhit_o       (datc_hit),
    .ibi_payload_o(ibi_payload),
    .ibi_reject_o (ibi_reject),
    .crr_reject_o (crr_reject),
    .xfer_mode_o  (xfer_mode),

    // Interface to DAT memory for walking the table.
    .dat_re_o     (datc_re),
    .dat_idx_o    (datc_idx),
    .dat_rdata_i  (dat_rdata_i)
  );

  // Retain the verdict of a DAT search that was performed as a result of an IBI or CRR winning
  // arbitration or the response to our attempted transfer.
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      nacked        <= 1'b0;
      ibi_xfer_mode <= XferMode_SDR0;
    end else if (enable_i) begin
      if (datc_req & datc_gnt) begin
        // Capture the information read from the DAT cache.
        nacked        <= arb_nack;
        ibi_xfer_mode <= xfer_mode;
      end else if ((state_q == WaitAckb) & trx_avalid_i) begin
        // Record whether the attempted transfer received an ACK or NACK response; we need this
        // information later, to ascertain whether the command should yet be completed.
        nacked        <= trx_arb_i.nack;
      end
    end
  end

  // -------------------------------- Debug Extended Capability ------------------------------------

  // - translate our FSM state information into the HCI-defined states.
  // - this mapping cannot be perfect due to implementation details but it's close.
  always_comb begin
    case (state_q)
      StartSDR:  bcl_tfr_ststat_o = BCLState_Start;
      RepStSDR:  bcl_tfr_ststat_o = BCLState_Restart;
      StopSDR:   bcl_tfr_ststat_o = BCLState_Stop;
      CmdWord:   bcl_tfr_ststat_o = BCLState_HDR;
      TxData:    bcl_tfr_ststat_o = BCLState_Wr;
      RxData:    bcl_tfr_ststat_o = BCLState_Rd;
      CmdAddr:   bcl_tfr_ststat_o = addr_bcst ? (cmd_attrs.rnw ? BCLState_BcastRead
                                                               : BCLState_BcastWrite)
                                              : BCLState_Addr;
      CmdArb,
      WaitArb:   bcl_tfr_ststat_o = addr_bcst ?
                               (cmd_attrs.rnw ? BCLState_BcastRead  : BCLState_BcastWrite) :
                          (trx_arb_i.arb_lost ? BCLState_IBIAdrRead : BCLState_Addr);
      CCC:       bcl_tfr_ststat_o = (cmd_attrs.attr == CmdAttr_AddrAssignment) ? BCLState_DAA
                                                                               : BCLState_CCC;
      CRR,
      HotJoin,
      IBICheck,
      IBIRxData,
      IBIRxWait: bcl_tfr_ststat_o = BCLState_IBIRead;
      default:   bcl_tfr_ststat_o = start_request ? BCLState_StartHold : BCLState_Idle;
    endcase
  end

  assign cmd_tid_o = cmd_attrs.tid;   // Transaction ID.

  // Detection and reporting of CE[3:0] error conditions.
  assign ctrl_error_o = {1'b0,
                         &{state_q == WaitAckb, addr_bcst, trx_arb_i.nack},  // No ACK to 7'h7e.
                         1'b0,
                         1'b0};
endmodule
