// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// OTP Controller top.
//

`include "prim_assert.sv"

module otp_ctrl
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0]        AlertAsyncOn = {NumAlerts{1'b1}},
  // TODO: These constants have to be replaced by the silicon creator before taping out.
  parameter logic [TimerWidth-1:0]       TimerLfsrSeed     = TimerWidth'(1'b1),
  parameter logic [TimerWidth-1:0][31:0] TimerLfsrPerm     = {
    32'd13, 32'd17, 32'd29, 32'd11, 32'd28, 32'd12, 32'd33, 32'd27,
    32'd05, 32'd39, 32'd31, 32'd21, 32'd15, 32'd01, 32'd24, 32'd37,
    32'd32, 32'd38, 32'd26, 32'd34, 32'd08, 32'd10, 32'd04, 32'd02,
    32'd19, 32'd00, 32'd20, 32'd06, 32'd25, 32'd22, 32'd03, 32'd35,
    32'd16, 32'd14, 32'd23, 32'd07, 32'd30, 32'd09, 32'd18, 32'd36
  }
) (
  input                                              clk_i,
  input                                              rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                          tl_i,
  output tlul_pkg::tl_d2h_t                          tl_o,
  // Interrupt Requests
  output logic                                       intr_otp_operation_done_o,
  output logic                                       intr_otp_error_o,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
  // Macro-specific power sequencing signals to/from AST.
  output otp_ast_req_t                               otp_ast_pwr_seq_o,
  input  otp_ast_rsp_t                               otp_ast_pwr_seq_h_i,
  // TODO: Refine and connect EDN interface
  output otp_edn_req_t                               otp_edn_o,
  input  otp_edn_rsp_t                               otp_edn_i,
  // Power manager interface (inputs are synced to OTP clock domain)
  input  pwrmgr_pkg::pwr_otp_req_t                   pwr_otp_i,
  output pwrmgr_pkg::pwr_otp_rsp_t                   pwr_otp_o,
  // Lifecycle transition command interface
  input  lc_otp_program_req_t                        lc_otp_program_i,
  output lc_otp_program_rsp_t                        lc_otp_program_o,
  // Lifecycle hashing interface for raw unlock
  input  lc_otp_token_req_t                          lc_otp_token_i,
  output lc_otp_token_rsp_t                          lc_otp_token_o,
  // Lifecycle broadcast inputs
  input  lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_provision_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_dft_en_i,
  // OTP broadcast outputs
  output otp_lc_data_t                               otp_lc_data_o,
  output otp_keymgr_key_t                            otp_keymgr_key_o,
  // Scrambling key requests
  input  flash_otp_key_req_t                         flash_otp_key_i,
  output flash_otp_key_rsp_t                         flash_otp_key_o,
  input  sram_otp_key_req_t [NumSramKeyReqSlots-1:0] sram_otp_key_i,
  output sram_otp_key_rsp_t [NumSramKeyReqSlots-1:0] sram_otp_key_o,
  input  otbn_otp_key_req_t                          otbn_otp_key_i,
  output otbn_otp_key_rsp_t                          otbn_otp_key_o,
  // Hardware config bits
  output logic [NumHwCfgBits-1:0]                    hw_cfg_o
);

  import prim_util_pkg::vbits;

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  // This ensures that we can transfer scrambler data blocks in and out of OTP atomically.
  `ASSERT_INIT(OtpIfWidth_A, OtpIfWidth == ScrmblBlockWidth)

  /////////////
  // Regfile //
  /////////////

  tlul_pkg::tl_h2d_t tl_win_h2d[2];
  tlul_pkg::tl_d2h_t tl_win_d2h[2];

  otp_ctrl_reg_pkg::otp_ctrl_reg2hw_t reg2hw;
  otp_ctrl_reg_pkg::otp_ctrl_hw2reg_t hw2reg;

  otp_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .tl_win_o  ( tl_win_h2d ),
    .tl_win_i  ( tl_win_d2h ),
    .reg2hw    ( reg2hw     ),
    .hw2reg    ( hw2reg     ),
    .devmode_i ( 1'b1       )
  );

  /////////////////////////////////////
  // TL-UL SW partition select logic //
  /////////////////////////////////////

  // The SW partitions share the same TL-UL adapter.
  logic tlul_req, tlul_gnt, tlul_rvalid;
  logic [SwWindowAddrWidth-1:0] tlul_addr;
  logic [1:0]  tlul_rerror;
  logic [31:0] tlul_rdata;

  tlul_adapter_sram #(
    .SramAw      ( SwWindowAddrWidth ),
    .SramDw      ( 32 ),
    .Outstanding ( 1  ),
    .ByteAccess  ( 0  ),
    .ErrOnWrite  ( 1  ) // No write accesses allowed here.
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i     ( tl_win_h2d[0] ),
    .tl_o     ( tl_win_d2h[0] ),
    .req_o    (  tlul_req     ),
    .gnt_i    (  tlul_gnt     ),
    .we_o     (               ), // unused
    .addr_o   (  tlul_addr    ),
    .wdata_o  (               ), // unused
    .wmask_o  (               ), // unused
    .rdata_i  (  tlul_rdata   ),
    .rvalid_i (  tlul_rvalid  ),
    .rerror_i (  tlul_rerror  )
  );

  logic [NumPart-1:0] tlul_part_sel_oh;
  for (genvar k = 0; k < NumPart; k++) begin : gen_part_sel
    localparam logic [OtpByteAddrWidth:0] PartEnd = (OtpByteAddrWidth+1)'(PartInfo[k].offset) +
                                                    (OtpByteAddrWidth+1)'(PartInfo[k].size);
    assign tlul_part_sel_oh[k] = ({tlul_addr, 2'b00} >= PartInfo[k].offset) &
                                 ({1'b0, {tlul_addr, 2'b00}} < PartEnd);
  end

  `ASSERT(PartSelMustBeOnehot_A, $onehot0(tlul_part_sel_oh))

  logic [NumPartWidth-1:0] tlul_part_idx;
  prim_arbiter_fixed #(
    .N(NumPart),
    .EnDataPort(0)
  ) u_part_sel_idx (
    .clk_i,
    .rst_ni,
    .req_i   ( tlul_part_sel_oh  ),
    .data_i  ( '{default: '0}    ),
    .gnt_o   (                   ), // unused
    .idx_o   ( tlul_part_idx     ),
    .valid_o (                   ), // unused
    .data_o  (                   ), // unused
    .ready_i ( 1'b0              )
  );

  logic tlul_oob_err_d, tlul_oob_err_q;
  logic [NumPart-1:0] part_tlul_req, part_tlul_gnt, part_tlul_rvalid;
  logic [SwWindowAddrWidth-1:0] part_tlul_addr;
  logic [NumPart-1:0][1:0]  part_tlul_rerror;
  logic [NumPart-1:0][31:0] part_tlul_rdata;

  always_comb begin : p_tlul_assign
    // Send request to the correct partition.
    part_tlul_addr   = tlul_addr;
    part_tlul_req    = '0;
    tlul_oob_err_d   = 1'b0;
    if (tlul_req) begin
      if (tlul_part_sel_oh != '0) begin
        part_tlul_req[tlul_part_idx] = 1'b1;
      end else begin
        // Error out in the next cycle if address was out of bounds.
        tlul_oob_err_d = 1'b1;
      end
    end

    // aggregate TL-UL responses
    tlul_gnt         = |part_tlul_gnt    | tlul_oob_err_q;
    tlul_rvalid      = |part_tlul_rvalid | tlul_oob_err_q;
    tlul_rerror      = '0;
    tlul_rdata       = '0;
    for (int k = 0; k < NumPart; k++) begin
      tlul_rerror |= part_tlul_rerror[k];
      tlul_rdata  |= part_tlul_rdata[k];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlul_reg
    if (!rst_ni) begin
      tlul_oob_err_q <= 1'b0;
    end else begin
      tlul_oob_err_q <= tlul_oob_err_d;
    end
  end

  ///////////////////////////////
  // Digests and LC State CSRs //
  ///////////////////////////////

  logic [ScrmblBlockWidth-1:0] unused_digest;
  logic [NumPart-1:0][ScrmblBlockWidth-1:0] part_digest;
  assign hw2reg.creator_sw_cfg_digest = part_digest[CreatorSwCfgIdx];
  assign hw2reg.owner_sw_cfg_digest   = part_digest[OwnerSwCfgIdx];
  assign hw2reg.hw_cfg_digest         = part_digest[HwCfgIdx];
  assign hw2reg.secret0_digest        = part_digest[Secret0Idx];
  assign hw2reg.secret1_digest        = part_digest[Secret1Idx];
  assign hw2reg.secret2_digest        = part_digest[Secret2Idx];
  // LC partition has no digest
  assign unused_digest                = part_digest[LifeCycleIdx];

  //////////////////////////////
  // Access Defaults and CSRs //
  //////////////////////////////

  part_access_t [NumPart-1:0] part_access_csrs;
  always_comb begin : p_access_control
    // Default (this will be overridden by partition-internal settings).
    part_access_csrs = {{32'(2*NumPart)}{Unlocked}};
    // Propagate CSR read enables down to the SW_CFG partitions.
    if (!reg2hw.creator_sw_cfg_read_lock) part_access_csrs[CreatorSwCfgIdx].read_lock = Locked;
    if (!reg2hw.owner_sw_cfg_read_lock) part_access_csrs[OwnerSwCfgIdx].read_lock = Locked;
    // The SECRET2 partition can only be accessed (write&read) when provisioning is enabled.
    if (lc_provision_en_i != lc_ctrl_pkg::On) part_access_csrs[Secret2Idx] = {2{Locked}};
    // Permanently lock DAI write access to the life cycle partition
    part_access_csrs[LifeCycleIdx].write_lock = Locked;
  end

  //////////////////////
  // DAI-related CSRs //
  //////////////////////

  logic                         dai_idle;
  logic                         dai_req;
  dai_cmd_e                     dai_cmd;
  logic [OtpByteAddrWidth-1:0]  dai_addr;
  logic [NumDaiWords-1:0][31:0] dai_wdata, dai_rdata;

  // Any write to this register triggers a DAI command.
  assign dai_req = reg2hw.direct_access_cmd.digest.qe |
                   reg2hw.direct_access_cmd.write.qe  |
                   reg2hw.direct_access_cmd.read.qe;

  assign dai_cmd = dai_cmd_e'({reg2hw.direct_access_cmd.digest.q,
                               reg2hw.direct_access_cmd.write.q,
                               reg2hw.direct_access_cmd.read.q});

  assign dai_addr  = reg2hw.direct_access_address.q;
  assign dai_wdata = reg2hw.direct_access_wdata;
  assign hw2reg.direct_access_rdata = dai_rdata;
  // This write-protects all DAI regs during pending operations.
  assign hw2reg.direct_access_regwen.d = dai_idle;

  // The DAI and the LCI can initiate write transactions, which
  // are critical and we must not power down if such transactions
  // are pending. Hence, we signal the LCI/DAI idle state to the
  // power manager. This signal is flopped here as it has to
  // cross a clock boundary to the power manager.
  logic lci_idle, otp_idle_d, otp_idle_q;
  assign otp_idle_d = lci_idle & dai_idle;
  assign pwr_otp_o.otp_idle = otp_idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_idle_reg
    if (!rst_ni) begin
      otp_idle_q <= 1'b0;
    end else begin
      otp_idle_q <= otp_idle_d;
    end
  end

  //////////////////////////////////////
  // Ctrl/Status CSRs, Errors, Alerts //
  //////////////////////////////////////

  // Status and error reporting CSRs, error interrupt generation and alerts.
  otp_err_e [NumPart+1:0] part_error;
  logic [NumPart+1:0] part_errors_reduced;
  logic otp_operation_done, otp_error;
  logic otp_fatal_error, otp_check_failed;
  logic chk_pending, chk_timeout;
  logic lfsr_fsm_err, key_deriv_fsm_err, scrmbl_fsm_err;
  always_comb begin : p_errors_alerts
    hw2reg.err_code = part_error;
    otp_fatal_error = 1'b0;
    otp_check_failed = 1'b0;
    // Aggregate all the errors from the partitions and the DAI/LCI
    for (int k = 0; k < NumPart+2; k++) begin
      // Set the error bit if the error status of the corresponding partition is nonzero.
      part_errors_reduced[k] = |part_error[k];
      // Filter for critical error codes that should not occur in the field.
      otp_fatal_error |= part_error[k] inside {OtpCmdInvErr,
                                               OtpInitErr,
                                               OtpReadUncorrErr,
                                               OtpReadErr,
                                               OtpWriteErr};

      // Filter for integrity and consistency check failures.
      otp_check_failed |= part_error[k] inside {ParityErr,
                                                IntegErr,
                                                CnstyErr,
                                                FsmErr} |
                          chk_timeout       |
                          lfsr_fsm_err      |
                          scrmbl_fsm_err    |
                          key_deriv_fsm_err;
    end
  end

  // Assign these to the status register.
  assign hw2reg.status = {chk_pending,
                          dai_idle,
                          key_deriv_fsm_err,
                          scrmbl_fsm_err,
                          lfsr_fsm_err,
                          chk_timeout,
                          part_errors_reduced};
  // If we got an error, we trigger an interrupt.
  assign otp_error = |part_errors_reduced | chk_timeout;

  //////////////////////////////////
  // Interrupts and Alert Senders //
  //////////////////////////////////

  prim_intr_hw #(
    .Width(1)
  ) u_intr_esc0 (
    .clk_i,
    .rst_ni,
    .event_intr_i           ( otp_operation_done                      ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.otp_operation_done.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.otp_operation_done.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.otp_operation_done.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.otp_operation_done.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.otp_operation_done.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.otp_operation_done.d  ),
    .intr_o                 ( intr_otp_operation_done_o               )
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_esc1 (
    .clk_i,
    .rst_ni,
    .event_intr_i           ( otp_error                      ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.otp_error.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.otp_error.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.otp_error.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.otp_error.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.otp_error.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.otp_error.d  ),
    .intr_o                 ( intr_otp_error_o               )
  );

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0])
  ) u_prim_alert_sender0 (
    .clk_i,
    .rst_ni,
    .alert_i    ( otp_fatal_error ),
    .alert_rx_i ( alert_rx_i[0] ),
    .alert_tx_o ( alert_tx_o[0] )
  );

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[1])
  ) u_prim_alert_sender1 (
    .clk_i,
    .rst_ni,
    .alert_i    ( otp_check_failed ),
    .alert_rx_i ( alert_rx_i[1] ),
    .alert_tx_o ( alert_tx_o[1] )
  );

  ////////////////////////////////
  // LFSR Timer and CSR mapping //
  ////////////////////////////////

  logic integ_chk_trig, cnsty_chk_trig;
  logic [NumPart-1:0] integ_chk_req, integ_chk_ack;
  logic [NumPart-1:0] cnsty_chk_req, cnsty_chk_ack;
  logic lfsr_edn_req, lfsr_edn_ack;

  assign integ_chk_trig   = reg2hw.check_trigger.integrity.q &
                            reg2hw.check_trigger.integrity.qe;
  assign cnsty_chk_trig   = reg2hw.check_trigger.consistency.q &
                            reg2hw.check_trigger.consistency.qe;

  otp_ctrl_lfsr_timer #(
    .LfsrSeed(TimerLfsrSeed),
    .LfsrPerm(TimerLfsrPerm)
  ) u_otp_ctrl_lfsr_timer (
    .clk_i,
    .rst_ni,
    .edn_req_o          ( lfsr_edn_req              ),
    .edn_ack_i          ( lfsr_edn_ack              ),
    .edn_data_i         ( otp_edn_i.data            ),
    // We can enable the timer once OTP has initialized.
    // Note that this is only the initial release that gets
    // the timer FSM into an operational state.
    // Whether or not the timers / background checks are
    // activated depends on the CSR configuration (by default
    // they are switched off).
    .timer_en_i         ( pwr_otp_o.otp_done        ),
    .integ_chk_trig_i   ( integ_chk_trig            ),
    .cnsty_chk_trig_i   ( cnsty_chk_trig            ),
    .chk_pending_o      ( chk_pending               ),
    .timeout_i          ( reg2hw.check_timeout.q    ),
    .integ_period_msk_i ( reg2hw.integrity_check_period.q   ),
    .cnsty_period_msk_i ( reg2hw.consistency_check_period.q ),
    .integ_chk_req_o    ( integ_chk_req             ),
    .cnsty_chk_req_o    ( cnsty_chk_req             ),
    .integ_chk_ack_i    ( integ_chk_ack             ),
    .cnsty_chk_ack_i    ( cnsty_chk_ack             ),
    .escalate_en_i      ( lc_escalate_en_i          ),
    .chk_timeout_o      ( chk_timeout               ),
    .fsm_err_o          ( lfsr_fsm_err              )
  );

  /////////////////////
  // EDN Arbitration //
  /////////////////////

  // Both the key derivation and LFSR reseeding are low bandwidth,
  // hence they can share the same EDN interface.
  logic key_edn_req, key_edn_ack;
  prim_arbiter_tree #(
    .N(2),
    .EnDataPort(0)
  ) u_edn_arb (
    .clk_i,
    .rst_ni,
    .req_i   ( {lfsr_edn_req, key_edn_req} ),
    .data_i  ( '{default: '0}              ),
    .gnt_o   ( {lfsr_edn_ack, key_edn_ack} ),
    .idx_o   (                             ), // unused
    .valid_o ( otp_edn_o.req               ),
    .data_o  (                             ), // unused
    .ready_i ( otp_edn_i.ack               )
  );

  ///////////////////////////////
  // OTP Macro and Arbitration //
  ///////////////////////////////

  typedef struct packed {
    prim_otp_cmd_e               cmd;
    logic [OtpSizeWidth-1:0]     size; // Number of native words to write.
    logic [OtpIfWidth-1:0]       wdata;
    logic [OtpAddrWidth-1:0]     addr; // Halfword address.
  } otp_bundle_t;

  logic [NumAgents-1:0]        part_otp_arb_req, part_otp_arb_gnt;
  otp_bundle_t                 part_otp_arb_bundle [NumAgents];
  logic                        otp_arb_valid, otp_arb_ready;
  logic [vbits(NumAgents)-1:0] otp_arb_idx;
  otp_bundle_t                 otp_arb_bundle;

  // The OTP interface is arbitrated on a per-cycle basis, meaning that back-to-back
  // transactions can be completely independent.
  prim_arbiter_tree #(
    .N(NumAgents),
    .DW($bits(otp_bundle_t))
  ) u_otp_arb (
    .clk_i,
    .rst_ni,
    .req_i   ( part_otp_arb_req    ),
    .data_i  ( part_otp_arb_bundle ),
    .gnt_o   ( part_otp_arb_gnt    ),
    .idx_o   ( otp_arb_idx         ),
    .valid_o ( otp_arb_valid       ),
    .data_o  ( otp_arb_bundle      ),
    .ready_i ( otp_arb_ready       )
  );

  otp_err_e              part_otp_err;
  logic [OtpIfWidth-1:0] part_otp_rdata;
  logic                  otp_rvalid;
  tlul_pkg::tl_h2d_t     tl_win_h2d_gated;
  tlul_pkg::tl_d2h_t     tl_win_d2h_gated;

  // Life cycle qualification of TL-UL test interface.
  assign tl_win_h2d_gated              = (lc_dft_en_i == lc_ctrl_pkg::On) ?
                                         tl_win_h2d[$high(tl_win_h2d)] : '0;
  assign tl_win_d2h[$high(tl_win_h2d)] = (lc_dft_en_i == lc_ctrl_pkg::On) ?
                                         tl_win_d2h_gated : '0;

  prim_otp #(
    .Width(OtpWidth),
    .Depth(OtpDepth)
  ) u_otp (
    .clk_i,
    .rst_ni,
    // Power sequencing signals to/from AST
    .pwr_seq_o   ( otp_ast_pwr_seq_o.pwr_seq     ),
    .pwr_seq_h_i ( otp_ast_pwr_seq_h_i.pwr_seq_h ),
    // Test interface
    .test_tl_i   ( tl_win_h2d_gated     ),
    .test_tl_o   ( tl_win_d2h_gated     ),
    // Read / Write command interface
    .ready_o     ( otp_arb_ready        ),
    .valid_i     ( otp_arb_valid        ),
    .cmd_i       ( otp_arb_bundle.cmd   ),
    .size_i      ( otp_arb_bundle.size  ),
    .addr_i      ( otp_arb_bundle.addr  ),
    .wdata_i     ( otp_arb_bundle.wdata ),
    // Read data out
    .valid_o     ( otp_rvalid           ),
    .rdata_o     ( part_otp_rdata       ),
    .err_o       ( part_otp_err         )
  );

  logic otp_fifo_valid;
  logic [vbits(NumAgents)-1:0] otp_part_idx;
  logic [NumAgents-1:0] part_otp_rvalid;

  // We can have up to two OTP commands in flight, hence we size this to be 2 deep.
  // The partitions can unconditionally sink requested data.
  prim_fifo_sync #(
    .Width(vbits(NumAgents)),
    .Depth(2)
  ) u_otp_rsp_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    ( 1'b0           ),
    .wvalid_i ( otp_arb_valid & otp_arb_ready ),
    .wready_o (                ),
    .wdata_i  ( otp_arb_idx    ),
    .rvalid_o ( otp_fifo_valid ),
    .rready_i ( otp_rvalid     ),
    .rdata_o  ( otp_part_idx   ),
    .depth_o  (                )
  );

  // Steer response back to the partition where this request originated.
  always_comb begin : p_rvalid
    part_otp_rvalid = '0;
    part_otp_rvalid[otp_part_idx] = otp_rvalid & otp_fifo_valid;
  end

  // Note that this must be true by construction.
  `ASSERT(OtpRespFifoUnderflow_A, otp_rvalid |-> otp_fifo_valid)

  /////////////////////////////////////////
  // Scrambling Datapath and Arbitration //
  /////////////////////////////////////////

  // Note: as opposed to the OTP arbitration above, we do not perform cycle-wise arbitration, but
  // transaction-wise arbitration. This is implemented using a RR arbiter that acts as a mutex.
  // I.e., each agent (e.g. the DAI or a partition) can request a lock on the mutex. Once granted,
  // the partition can keep the the lock as long as needed for the transaction to complete. The
  // partition must yield its lock by deasserting the request signal for the arbiter to proceed.
  // Since this scheme does not have built-in preemtion, it must be ensured that the agents
  // eventually release their locks for this to be fair.
  //
  // See also https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#block-diagram for details.
  typedef struct packed {
    otp_scrmbl_cmd_e             cmd;
    logic [ConstSelWidth-1:0]    sel;
    logic [ScrmblBlockWidth-1:0] data;
    logic                        valid;
  } scrmbl_bundle_t;

  logic [NumAgents-1:0]        part_scrmbl_mtx_req, part_scrmbl_mtx_gnt;
  scrmbl_bundle_t              part_scrmbl_req_bundle [NumAgents];
  scrmbl_bundle_t              scrmbl_req_bundle;
  logic [vbits(NumAgents)-1:0] scrmbl_mtx_idx;
  logic                        scrmbl_mtx_valid;

  // Note that arbiter decisions do not change when backpressured.
  // Hence, the idx_o signal is guaranteed to remain stable until ack'ed.
  prim_arbiter_tree #(
    .N(NumAgents),
    .DW($bits(scrmbl_bundle_t)),
    .EnReqStabA(0)
  ) u_scrmbl_mtx (
    .clk_i,
    .rst_ni,
    .req_i   ( part_scrmbl_mtx_req  ),
    .data_i  ( part_scrmbl_req_bundle ),
    .gnt_o   (                        ),
    .idx_o   ( scrmbl_mtx_idx         ),
    .valid_o ( scrmbl_mtx_valid       ),
    .data_o  ( scrmbl_req_bundle      ),
    .ready_i ( 1'b0                   )
  );

  // Since the ready_i signal of the arbiter is statically set to 1'b0 above, we are always in a
  // "backpressure" situation, where the RR arbiter will automatically advance the internal RR state
  // to give the current winner max priority in subsequent cycles in order to keep the decision
  // stable. Rearbitration occurs once the winning agent deasserts its request.
  always_comb begin : p_mutex
    part_scrmbl_mtx_gnt = '0;
    part_scrmbl_mtx_gnt[scrmbl_mtx_idx] = scrmbl_mtx_valid;
  end

  logic [ScrmblBlockWidth-1:0] part_scrmbl_rsp_data;
  logic scrmbl_arb_req_ready, scrmbl_arb_rsp_valid;
  logic [NumAgents-1:0] part_scrmbl_req_ready, part_scrmbl_rsp_valid;

  otp_ctrl_scrmbl u_scrmbl (
    .clk_i,
    .rst_ni,
    .cmd_i         ( scrmbl_req_bundle.cmd   ),
    .sel_i         ( scrmbl_req_bundle.sel   ),
    .data_i        ( scrmbl_req_bundle.data  ),
    .valid_i       ( scrmbl_req_bundle.valid ),
    .ready_o       ( scrmbl_arb_req_ready    ),
    .data_o        ( part_scrmbl_rsp_data    ),
    .valid_o       ( scrmbl_arb_rsp_valid    ),
    .escalate_en_i ( lc_escalate_en_i        ),
    .fsm_err_o     ( scrmbl_fsm_err          )
  );

  // steer back responses
  always_comb begin : p_scmrbl_resp
    part_scrmbl_req_ready = '0;
    part_scrmbl_rsp_valid = '0;
    part_scrmbl_req_ready[scrmbl_mtx_idx] = scrmbl_arb_req_ready;
    part_scrmbl_rsp_valid[scrmbl_mtx_idx] = scrmbl_arb_rsp_valid;
  end

  /////////////////////////////
  // Direct Access Interface //
  /////////////////////////////

  logic                           part_init_req;
  logic [NumPart-1:0]             part_init_done;
  part_access_t [NumPart-1:0]     part_access_dai;

  // The init request comes from the power manager, which lives in the AON clock domain.
  logic pwr_otp_req_synced;
  prim_flop_2sync #(
    .Width(1)
  ) u_otp_init_sync (
    .clk_i,
    .rst_ni,
    .d_i ( pwr_otp_i.otp_init ),
    .q_o ( pwr_otp_req_synced )
  );

  // Register this signal as it has to cross a clock boundary.
  logic pwr_otp_rsp_d, pwr_otp_rsp_q;
  assign pwr_otp_o.otp_done = pwr_otp_rsp_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_init_reg
    if (!rst_ni) begin
      pwr_otp_rsp_q <= 1'b0;
    end else begin
      pwr_otp_rsp_q <= pwr_otp_rsp_d;
    end
  end

  otp_ctrl_dai u_otp_ctrl_dai (
    .clk_i,
    .rst_ni,
    .init_req_i       ( pwr_otp_req_synced                    ),
    .init_done_o      ( pwr_otp_rsp_d                         ),
    .part_init_req_o  ( part_init_req                         ),
    .part_init_done_i ( part_init_done                        ),
    .escalate_en_i    ( lc_escalate_en_i                      ),
    .error_o          ( part_error[DaiIdx]                    ),
    .part_access_i    ( part_access_dai                       ),
    .dai_addr_i       ( dai_addr                              ),
    .dai_cmd_i        ( dai_cmd                               ),
    .dai_req_i        ( dai_req                               ),
    .dai_wdata_i      ( dai_wdata                             ),
    .dai_idle_o       ( dai_idle                              ),
    .dai_cmd_done_o   ( otp_operation_done                    ),
    .dai_rdata_o      ( dai_rdata                             ),
    .otp_req_o        ( part_otp_arb_req[DaiIdx]              ),
    .otp_cmd_o        ( part_otp_arb_bundle[DaiIdx].cmd       ),
    .otp_size_o       ( part_otp_arb_bundle[DaiIdx].size      ),
    .otp_wdata_o      ( part_otp_arb_bundle[DaiIdx].wdata     ),
    .otp_addr_o       ( part_otp_arb_bundle[DaiIdx].addr      ),
    .otp_gnt_i        ( part_otp_arb_gnt[DaiIdx]              ),
    .otp_rvalid_i     ( part_otp_rvalid[DaiIdx]               ),
    .otp_rdata_i      ( part_otp_rdata                        ),
    .otp_err_i        ( part_otp_err                          ),
    .scrmbl_mtx_req_o ( part_scrmbl_mtx_req[DaiIdx]           ),
    .scrmbl_mtx_gnt_i ( part_scrmbl_mtx_gnt[DaiIdx]           ),
    .scrmbl_cmd_o     ( part_scrmbl_req_bundle[DaiIdx].cmd    ),
    .scrmbl_sel_o     ( part_scrmbl_req_bundle[DaiIdx].sel    ),
    .scrmbl_data_o    ( part_scrmbl_req_bundle[DaiIdx].data   ),
    .scrmbl_valid_o   ( part_scrmbl_req_bundle[DaiIdx].valid  ),
    .scrmbl_ready_i   ( part_scrmbl_req_ready[DaiIdx]         ),
    .scrmbl_valid_i   ( part_scrmbl_rsp_valid[DaiIdx]         ),
    .scrmbl_data_i    ( part_scrmbl_rsp_data                  )
  );

  ////////////////////////////////////
  // Lifecycle Transition Interface //
  ////////////////////////////////////

  otp_ctrl_lci #(
    .Info(PartInfo[LifeCycleIdx])
  ) u_otp_ctrl_lci (
    .clk_i,
    .rst_ni,
    .lci_en_i         ( pwr_otp_o.otp_done                ),
    .escalate_en_i    ( lc_escalate_en_i                  ),
    .error_o          ( part_error[LciIdx]                ),
    .lci_idle_o       ( lci_idle                          ),
    .lc_req_i         ( lc_otp_program_i.req              ),
    .lc_state_delta_i ( lc_otp_program_i.state_delta      ),
    .lc_count_delta_i ( lc_otp_program_i.count_delta      ),
    .lc_ack_o         ( lc_otp_program_o.ack              ),
    .lc_err_o         ( lc_otp_program_o.err              ),
    .otp_req_o        ( part_otp_arb_req[LciIdx]          ),
    .otp_cmd_o        ( part_otp_arb_bundle[LciIdx].cmd   ),
    .otp_size_o       ( part_otp_arb_bundle[LciIdx].size  ),
    .otp_wdata_o      ( part_otp_arb_bundle[LciIdx].wdata ),
    .otp_addr_o       ( part_otp_arb_bundle[LciIdx].addr  ),
    .otp_gnt_i        ( part_otp_arb_gnt[LciIdx]          ),
    .otp_rvalid_i     ( part_otp_rvalid[LciIdx]           ),
    .otp_rdata_i      ( part_otp_rdata                    ),
    .otp_err_i        ( part_otp_err                      )
  );

  // Tie off unused connections.
  assign part_scrmbl_mtx_req[LciIdx]    = '0;
  assign part_scrmbl_req_bundle[LciIdx] = '0;

  // This stops lint from complaining about unused signals.
  logic unused_lci_scrmbl_sigs;
  assign unused_lci_scrmbl_sigs = ^{part_scrmbl_mtx_gnt[LciIdx],
                                    part_scrmbl_req_ready[LciIdx],
                                    part_scrmbl_rsp_valid[LciIdx]};

  ////////////////////////////////////
  // Key Derivation Interface (KDI) //
  ////////////////////////////////////

  logic scrmbl_key_seed_valid;
  logic [SramKeySeedWidth-1:0] sram_data_key_seed;
  logic [FlashKeySeedWidth-1:0] flash_data_key_seed, flash_addr_key_seed;

  otp_ctrl_kdi i_otp_ctrl_kdi (
    .clk_i,
    .rst_ni,
    .kdi_en_i                ( pwr_otp_o.otp_done      ),
    .escalate_en_i           ( lc_escalate_en_i        ),
    .fsm_err_o               ( key_deriv_fsm_err       ),
    .scrmbl_key_seed_valid_i ( scrmbl_key_seed_valid   ),
    .flash_data_key_seed_i   ( flash_data_key_seed     ),
    .flash_addr_key_seed_i   ( flash_addr_key_seed     ),
    .sram_data_key_seed_i    ( sram_data_key_seed      ),
    .edn_req_o               ( key_edn_req             ),
    .edn_ack_i               ( key_edn_ack             ),
    .edn_data_i              ( otp_edn_i.data          ),
    .lc_otp_token_i ,
    .lc_otp_token_o ,
    .flash_otp_key_i,
    .flash_otp_key_o,
    .sram_otp_key_i,
    .sram_otp_key_o,
    .otbn_otp_key_i,
    .otbn_otp_key_o,
    .scrmbl_mtx_req_o        ( part_scrmbl_mtx_req[KdiIdx]          ),
    .scrmbl_mtx_gnt_i        ( part_scrmbl_mtx_gnt[KdiIdx]          ),
    .scrmbl_cmd_o            ( part_scrmbl_req_bundle[KdiIdx].cmd   ),
    .scrmbl_sel_o            ( part_scrmbl_req_bundle[KdiIdx].sel   ),
    .scrmbl_data_o           ( part_scrmbl_req_bundle[KdiIdx].data  ),
    .scrmbl_valid_o          ( part_scrmbl_req_bundle[KdiIdx].valid ),
    .scrmbl_ready_i          ( part_scrmbl_req_ready[KdiIdx]        ),
    .scrmbl_valid_i          ( part_scrmbl_rsp_valid[KdiIdx]        ),
    .scrmbl_data_i           ( part_scrmbl_rsp_data                 )
  );

  // Tie off OTP bus access, since this is not needed.
  assign part_otp_arb_req[KdiIdx] = 1'b0;
  assign part_otp_arb_bundle[KdiIdx] = '0;

  // This stops lint from complaining about unused signals.
  logic unused_kdi_otp_sigs;
  assign unused_kdi_otp_sigs = ^{part_otp_arb_gnt[KdiIdx],
                                 part_otp_rvalid[KdiIdx]};

  /////////////////////////
  // Partition Instances //
  /////////////////////////

  logic [2**OtpByteAddrWidth-1:0][7:0] part_buf_data;

  for (genvar k = 0; k < NumPart; k ++) begin : gen_partitions
    ////////////////////////////////////////////////////////////////////////////////////////////////
    if (PartInfo[k].variant == Unbuffered) begin : gen_unbuffered
      otp_ctrl_part_unbuf #(
        .Info(PartInfo[k])
      ) u_part_unbuf (
        .clk_i,
        .rst_ni,
        .init_req_i    ( part_init_req                ),
        .init_done_o   ( part_init_done[k]            ),
        .escalate_en_i ( lc_escalate_en_i             ),
        .error_o       ( part_error[k]                ),
        .access_i      ( part_access_csrs[k]          ),
        .access_o      ( part_access_dai[k]           ),
        .digest_o      ( part_digest[k]               ),
        .tlul_req_i    ( part_tlul_req[k]             ),
        .tlul_gnt_o    ( part_tlul_gnt[k]             ),
        .tlul_addr_i   ( part_tlul_addr               ),
        .tlul_rerror_o ( part_tlul_rerror[k]          ),
        .tlul_rvalid_o ( part_tlul_rvalid[k]          ),
        .tlul_rdata_o  ( part_tlul_rdata[k]           ),
        .otp_req_o     ( part_otp_arb_req[k]          ),
        .otp_cmd_o     ( part_otp_arb_bundle[k].cmd   ),
        .otp_size_o    ( part_otp_arb_bundle[k].size  ),
        .otp_wdata_o   ( part_otp_arb_bundle[k].wdata ),
        .otp_addr_o    ( part_otp_arb_bundle[k].addr  ),
        .otp_gnt_i     ( part_otp_arb_gnt[k]          ),
        .otp_rvalid_i  ( part_otp_rvalid[k]           ),
        .otp_rdata_i   ( part_otp_rdata               ),
        .otp_err_i     ( part_otp_err                 )
      );

      // Tie off unused connections.
      assign part_scrmbl_mtx_req[k]    = '0;
      assign part_scrmbl_req_bundle[k] = '0;
      // These checks do not exist in this partition type,
      // so we always acknowledge the request.
      assign integ_chk_ack[k]          = 1'b1;
      assign cnsty_chk_ack[k]          = 1'b1;

      // No buffered data to expose.
      assign part_buf_data[PartInfo[k].offset +: PartInfo[k].size] = '0;

      // This stops lint from complaining about unused signals.
      logic unused_part_scrmbl_sigs;
      assign unused_part_scrmbl_sigs = ^{part_scrmbl_mtx_gnt[k],
                                         part_scrmbl_req_ready[k],
                                         part_scrmbl_rsp_valid[k],
                                         integ_chk_req[k],
                                         cnsty_chk_req[k]};

    ////////////////////////////////////////////////////////////////////////////////////////////////
    end else if (PartInfo[k].variant == Buffered) begin : gen_buffered
      otp_ctrl_part_buf #(
        .Info(PartInfo[k])
      ) u_part_buf (
        .clk_i,
        .rst_ni,
        .init_req_i       ( part_init_req                   ),
        .init_done_o      ( part_init_done[k]               ),
        .integ_chk_req_i  ( integ_chk_req[k]                ),
        .integ_chk_ack_o  ( integ_chk_ack[k]                ),
        .cnsty_chk_req_i  ( cnsty_chk_req[k]                ),
        .cnsty_chk_ack_o  ( cnsty_chk_ack[k]                ),
        .escalate_en_i    ( lc_escalate_en_i                ),
        .error_o          ( part_error[k]                   ),
        .access_i         ( part_access_csrs[k]             ),
        .access_o         ( part_access_dai[k]              ),
        .digest_o         ( part_digest[k]                  ),
        .data_o           ( part_buf_data[PartInfo[k].offset +: PartInfo[k].size] ),
        .otp_req_o        ( part_otp_arb_req[k]             ),
        .otp_cmd_o        ( part_otp_arb_bundle[k].cmd      ),
        .otp_size_o       ( part_otp_arb_bundle[k].size     ),
        .otp_wdata_o      ( part_otp_arb_bundle[k].wdata    ),
        .otp_addr_o       ( part_otp_arb_bundle[k].addr     ),
        .otp_gnt_i        ( part_otp_arb_gnt[k]             ),
        .otp_rvalid_i     ( part_otp_rvalid[k]              ),
        .otp_rdata_i      ( part_otp_rdata                  ),
        .otp_err_i        ( part_otp_err                    ),
        .scrmbl_mtx_req_o ( part_scrmbl_mtx_req[k]          ),
        .scrmbl_mtx_gnt_i ( part_scrmbl_mtx_gnt[k]          ),
        .scrmbl_cmd_o     ( part_scrmbl_req_bundle[k].cmd   ),
        .scrmbl_sel_o     ( part_scrmbl_req_bundle[k].sel   ),
        .scrmbl_data_o    ( part_scrmbl_req_bundle[k].data  ),
        .scrmbl_valid_o   ( part_scrmbl_req_bundle[k].valid ),
        .scrmbl_ready_i   ( part_scrmbl_req_ready[k]        ),
        .scrmbl_valid_i   ( part_scrmbl_rsp_valid[k]        ),
        .scrmbl_data_i    ( part_scrmbl_rsp_data            )
      );

      // Buffered partitions are not accessible via the TL-UL window.
      logic unused_part_tlul_sigs;
      assign unused_part_tlul_sigs = ^part_tlul_req[k];
      assign part_tlul_gnt[k]    = 1'b0;
      assign part_tlul_rerror[k] = '0;
      assign part_tlul_rvalid[k] = 1'b0;
      assign part_tlul_rdata[k]  = '0;

    end else begin : gen_invalid
      // This is invalid and should break elaboration
      assert_static_in_generate_invalid assert_static_in_generate_invalid();
    end
  end

  //////////////////////////////////
  // Buffered Data Output Mapping //
  //////////////////////////////////

  // TODO: template these mappings, based on the address map hjson contents.

  // Output complete hardware config partition.
  // Actual mapping to other IPs can occur at the top-level.
  assign hw_cfg_o = part_buf_data[PartInfo[HwCfgIdx].offset +:
                                  PartInfo[HwCfgIdx].size];

  // Root keys
  assign otp_keymgr_key_o.valid = part_init_done[Secret2Idx];
  assign {otp_keymgr_key_o.key_share1,
          otp_keymgr_key_o.key_share0} = part_buf_data[PartInfo[Secret2Idx].offset +:
                                                       2*KeyMgrKeyWidth/8];
  // Scrambling Keys
  assign scrmbl_key_seed_valid = part_init_done[Secret1Idx];
  assign {sram_data_key_seed,
          flash_data_key_seed,
          flash_addr_key_seed} = part_buf_data[PartInfo[Secret1Idx].offset +:
                                               2*FlashKeySeedWidth/8 +
                                               SramKeySeedWidth/8];
  // Test unlock and exit tokens
  assign {otp_lc_data_o.test_exit_token,
          otp_lc_data_o.test_unlock_token} = part_buf_data[PartInfo[Secret0Idx].offset +:
                                                           2*lc_ctrl_pkg::LcTokenWidth/8];
  // RMA token
  assign otp_lc_data_o.rma_token      = part_buf_data[PartInfo[Secret2Idx].offset +:
                                                        lc_ctrl_pkg::LcTokenWidth/8];
  // The device is personalized if the root key has been provisioned and locked
  assign otp_lc_data_o.id_state       = (part_digest[Secret2Idx] != '0) ? lc_ctrl_pkg::Set :
                                                                          lc_ctrl_pkg::Blk;

  // Lifecycle state
  assign {otp_lc_data_o.count,
          otp_lc_data_o.state}        = part_buf_data[PartInfo[LifeCycleIdx].offset +:
                                                      PartInfo[LifeCycleIdx].size];

  // Assert life cycle state valid signal only when all partitions have initialized.
  assign otp_lc_data_o.valid    = &part_init_done;

  // Not all bits of part_buf_data are used here.
  logic unused_buf_data;
  assign unused_buf_data = ^part_buf_data;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(OtpAstPwrSeqKnown_A,         otp_ast_pwr_seq_o)
  `ASSERT_KNOWN(TlOutKnown_A,                tl_o)
  `ASSERT_KNOWN(IntrOtpOperationDoneKnown_A, intr_otp_operation_done_o)
  `ASSERT_KNOWN(IntrOtpErrorKnown_A,         intr_otp_error_o)
  `ASSERT_KNOWN(AlertTxKnown_A,              alert_tx_o)
  `ASSERT_KNOWN(PwrOtpInitRspKnown_A,        pwr_otp_o)
  `ASSERT_KNOWN(LcOtpProgramRspKnown_A,      lc_otp_program_o)
  `ASSERT_KNOWN(OtpLcDataKnown_A,            otp_lc_data_o)
  `ASSERT_KNOWN(OtpKeymgrKeyKnown_A,         otp_keymgr_key_o)
  `ASSERT_KNOWN(FlashOtpKeyRspKnown_A,       flash_otp_key_o)
  `ASSERT_KNOWN(OtpSramKeyKnown_A,           sram_otp_key_o)
  `ASSERT_KNOWN(OtpOtgnKeyKnown_A,           otbn_otp_key_o)
  `ASSERT_KNOWN(HwCfgKnown_A,                hw_cfg_o)

endmodule : otp_ctrl
