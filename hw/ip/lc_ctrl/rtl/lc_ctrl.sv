// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle controller top.
//

`include "prim_assert.sv"

module lc_ctrl
  import lc_ctrl_pkg::*;
  import lc_ctrl_reg_pkg::*;
  import lc_ctrl_state_pkg::*;
#(
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Idcode value for the JTAG.
  parameter logic [31:0]          IdcodeValue  = 32'h00000001,
  // Random netlist constants
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid    = LcKeymgrDivWidth'(0),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestDevRma = LcKeymgrDivWidth'(1),
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction = LcKeymgrDivWidth'(2)
) (
  // Life cycle controller clock
  input                                              clk_i,
  input                                              rst_ni,
  // Clock for KMAC interface
  input                                              clk_kmac_i,
  input                                              rst_kmac_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                          tl_i,
  output tlul_pkg::tl_d2h_t                          tl_o,
  // JTAG TAP.
  input  jtag_pkg::jtag_req_t                        jtag_i,
  output jtag_pkg::jtag_rsp_t                        jtag_o,
  // This bypasses the clock inverter inside the JTAG TAP for scanmmode.
  input                                              scan_rst_ni,
  input  lc_tx_t                                     scanmode_i,
  // Alert outputs.
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
  // Escalation inputs (severity 1 and 2).
  // These need not be synchronized since the alert handler is
  // in the same clock domain as the LC controller.
  input  prim_esc_pkg::esc_rx_t                      esc_wipe_secrets_tx_i,
  output prim_esc_pkg::esc_tx_t                      esc_wipe_secrets_rx_o,
  input  prim_esc_pkg::esc_rx_t                      esc_scrap_state_tx_i,
  output prim_esc_pkg::esc_tx_t                      esc_scrap_state_rx_o,
  // Power manager interface (inputs are synced to lifecycle clock domain).
  input  pwrmgr_pkg::pwr_lc_req_t                    pwr_lc_i,
  output pwrmgr_pkg::pwr_lc_rsp_t                    pwr_lc_o,
  // Life cycle transition command interface.
  // No sync required since LC and OTP are in the same clock domain.
  output otp_ctrl_pkg::lc_otp_program_req_t          lc_otp_program_o,
  input  otp_ctrl_pkg::lc_otp_program_rsp_t          lc_otp_program_i,
  // Life cycle hashing interface for raw unlock
  // Synchronized in the life cycle controller.
  input  kmac_pkg::app_rsp_t                         kmac_data_i,
  output kmac_pkg::app_req_t                         kmac_data_o,
  // OTP broadcast outputs
  // No sync required since LC and OTP are in the same clock domain.
  input  otp_ctrl_pkg::otp_lc_data_t                 otp_lc_data_i,
  // Life cycle broadcast outputs (all of them are registered).
  output lc_tx_t                                     lc_dft_en_o,
  output lc_tx_t                                     lc_nvm_debug_en_o,
  output lc_tx_t                                     lc_hw_debug_en_o,
  output lc_tx_t                                     lc_cpu_en_o,
  output lc_tx_t                                     lc_creator_seed_sw_rw_en_o,
  output lc_tx_t                                     lc_owner_seed_sw_rw_en_o,
  output lc_tx_t                                     lc_iso_part_sw_rd_en_o,
  output lc_tx_t                                     lc_iso_part_sw_wr_en_o,
  output lc_tx_t                                     lc_seed_hw_rd_en_o,
  output lc_tx_t                                     lc_keymgr_en_o,
  output lc_tx_t                                     lc_escalate_en_o,
  output lc_tx_t                                     lc_check_byp_en_o,
  // Request and feedback to/from clock manager and AST.
  // The ack is synced to the lc clock domain using prim_lc_sync.
  output lc_tx_t                                     lc_clk_byp_req_o,
  input  lc_tx_t                                     lc_clk_byp_ack_i,
  // Request and feedback to/from flash controller.
  // The ack is synced to the lc clock domain using prim_lc_sync.
  output lc_flash_rma_seed_t                         lc_flash_rma_seed_o,
  output lc_tx_t                                     lc_flash_rma_req_o,
  input  lc_tx_t                                     lc_flash_rma_ack_i,
  // State group diversification value for keymgr.
  output lc_keymgr_div_t                             lc_keymgr_div_o,
  // Hardware config input, needed for the DEVICE_ID field.
  input  otp_ctrl_pkg::otp_device_id_t               otp_device_id_i
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  // Check that the CSR parameters correspond with the ones used in the design.
  `ASSERT_INIT(DecLcStateWidthCheck_A, CsrLcStateWidth == DecLcStateWidth)
  `ASSERT_INIT(DecLcCountWidthCheck_A, CsrLcCountWidth == DecLcCountWidth)
  `ASSERT_INIT(DecLcIdStateWidthCheck_A, CsrLcIdStateWidth == DecLcIdStateWidth)
  `ASSERT_INIT(NumTokenWordsCheck_A, NumTokenWords == LcTokenWidth/32)

  /////////////
  // Regfile //
  /////////////

  lc_ctrl_reg_pkg::lc_ctrl_reg2hw_t reg2hw;
  lc_ctrl_reg_pkg::lc_ctrl_hw2reg_t hw2reg;

  lc_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw    ( reg2hw ),
    .hw2reg    ( hw2reg ),
    .intg_err_o(        ),
    .devmode_i ( 1'b1   )
  );

  ////////////////////
  // Life Cycle TAP //
  ////////////////////

  tlul_pkg::tl_h2d_t tap_tl_h2d;
  tlul_pkg::tl_d2h_t tap_tl_d2h;
  lc_ctrl_reg_pkg::lc_ctrl_reg2hw_t tap_reg2hw;
  lc_ctrl_reg_pkg::lc_ctrl_hw2reg_t tap_hw2reg;

  lc_ctrl_reg_top u_reg_tap (
    .clk_i,
    .rst_ni,
    .tl_i      ( tap_tl_h2d ),
    .tl_o      ( tap_tl_d2h ),
    .reg2hw    ( tap_reg2hw ),
    .hw2reg    ( tap_hw2reg ),
    .intg_err_o(            ),
    .devmode_i ( 1'b1       )
  );


  // This reuses the JTAG DTM and DMI from the RISC-V external
  // debug v0.13 specification to read and write the lc_ctrl CSRs:
  // https://github.com/riscv/riscv-debug-spec/blob/release/riscv-debug-release.pdf
  // The register addresses correspond to the byte offsets of the lc_ctrl CSRs, divided by 4.
  // Note that the DMI reset does not affect the LC controller in any way.
  dm::dmi_req_t dmi_req;
  logic dmi_req_valid;
  logic dmi_req_ready;
  dm::dmi_resp_t dmi_resp;
  logic dmi_resp_ready;
  logic dmi_resp_valid;

  logic scanmode;
  assign scanmode = (scanmode_i == On);

  logic tck_muxed;
  logic trst_n_muxed;
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_clock_mux2 (
    .clk0_i(jtag_i.tck),
    .clk1_i(clk_i),
    .sel_i (scanmode),
    .clk_o (tck_muxed)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_rst_n_mux2 (
    .clk0_i(jtag_i.trst_n),
    .clk1_i(scan_rst_ni),
    .sel_i (scanmode),
    .clk_o (trst_n_muxed)
  );

  logic req_ready;
  assign req_ready = dmi_req_ready & dmi_resp_ready;
  dmi_jtag #(
    .IdcodeValue(IdcodeValue)
  ) u_dmi_jtag (
    .clk_i,
    .rst_ni,
    .testmode_i       ( scanmode          ),
    .dmi_rst_no       (                   ), // unused
    .dmi_req_o        ( dmi_req           ),
    .dmi_req_valid_o  ( dmi_req_valid     ),
    // unless there is room for response, stall
    .dmi_req_ready_i  ( req_ready         ),
    .dmi_resp_i       ( dmi_resp          ),
    .dmi_resp_ready_o ( dmi_resp_ready    ),
    .dmi_resp_valid_i ( dmi_resp_valid    ),
    .tck_i            ( tck_muxed         ),
    .tms_i            ( jtag_i.tms        ),
    .trst_ni          ( trst_n_muxed      ),
    .td_i             ( jtag_i.tdi        ),
    .td_o             ( jtag_o.tdo        ),
    .tdo_oe_o         ( jtag_o.tdo_oe     )
  );

  // DMI to TL-UL transducing
  tlul_adapter_host u_tap_tlul_host (
    .clk_i,
    .rst_ni,
    // do not make a request unless there is room for the response
    .req_i      ( dmi_req_valid & dmi_resp_ready         ),
    .gnt_o      ( dmi_req_ready                          ),
    .addr_i     ( top_pkg::TL_AW'({dmi_req.addr, 2'b00}) ),
    .we_i       ( dmi_req.op == dm::DTM_WRITE            ),
    .wdata_i    ( dmi_req.data                           ),
    .be_i       ( {top_pkg::TL_DBW{1'b1}}                ),
    .type_i     ( tlul_pkg::DataType                     ),
    .valid_o    ( dmi_resp_valid                         ),
    .rdata_o    ( dmi_resp.data                          ),
    .err_o      (                                        ),
    .intg_err_o (                                        ),
    .tl_o       ( tap_tl_h2d                             ),
    .tl_i       ( tap_tl_d2h                             )
  );

  // TL-UL to DMI transducing
  assign dmi_resp.resp = '0; // unused inside dmi_jtag

  // These signals are unused
  logic unused_tap_tl_d2h;
  assign unused_tap_tl_d2h = ^{
    tap_tl_d2h.d_opcode,
    tap_tl_d2h.d_param,
    tap_tl_d2h.d_size,
    tap_tl_d2h.d_source,
    tap_tl_d2h.d_sink,
    tap_tl_d2h.d_user,
    tap_tl_d2h.d_error
  };

  ///////////////////////////////////////
  // Transition Interface and HW Mutex //
  ///////////////////////////////////////

  // All registers are HWext
  logic          trans_success_d, trans_success_q;
  logic          trans_cnt_oflw_error_d, trans_cnt_oflw_error_q;
  logic          trans_invalid_error_d, trans_invalid_error_q;
  logic          token_invalid_error_d, token_invalid_error_q;
  logic          flash_rma_error_d, flash_rma_error_q;
  logic          otp_prog_error_d, fatal_prog_error_q;
  logic          state_invalid_error_d, fatal_state_error_q;
  logic          otp_part_error_q;
  logic [7:0]    sw_claim_transition_if_d, sw_claim_transition_if_q;
  logic [7:0]    tap_claim_transition_if_d, tap_claim_transition_if_q;
  logic          transition_cmd;
  lc_token_t     transition_token_d, transition_token_q;
  dec_lc_state_e transition_target_d, transition_target_q;
  // No need to register these.
  dec_lc_state_e    dec_lc_state;
  dec_lc_cnt_t      dec_lc_cnt;
  dec_lc_id_state_e dec_lc_id_state;

  logic lc_idle_d;

  always_comb begin : p_csr_assign_outputs
    hw2reg = '0;
    hw2reg.status.ready                  = lc_idle_d;
    hw2reg.status.transition_successful  = trans_success_q;
    hw2reg.status.transition_count_error = trans_cnt_oflw_error_q;
    hw2reg.status.transition_error       = trans_invalid_error_q;
    hw2reg.status.token_error            = token_invalid_error_q;
    hw2reg.status.flash_rma_error        = flash_rma_error_q;
    hw2reg.status.otp_error              = fatal_prog_error_q;
    hw2reg.status.state_error            = fatal_state_error_q;
    hw2reg.status.otp_partition_error    = otp_part_error_q;
    hw2reg.lc_state                      = dec_lc_state;
    hw2reg.lc_transition_cnt             = dec_lc_cnt;
    hw2reg.lc_id_state                   = dec_lc_id_state;
    hw2reg.device_id                     = otp_device_id_i;

    // The assignments above are identical for the TAP.
    tap_hw2reg = hw2reg;

    // Assignments gated by mutex.
    hw2reg.claim_transition_if = sw_claim_transition_if_q;
    if (sw_claim_transition_if_q == 8'hA5) begin
      hw2reg.transition_token  = transition_token_q;
      hw2reg.transition_target = transition_target_q;
      hw2reg.transition_regwen = lc_idle_d;
    end

    tap_hw2reg.claim_transition_if = tap_claim_transition_if_q;
    if (tap_claim_transition_if_q == 8'hA5) begin
      tap_hw2reg.transition_token  = transition_token_q;
      tap_hw2reg.transition_target = transition_target_q;
      tap_hw2reg.transition_regwen = lc_idle_d;
    end
  end

  always_comb begin : p_csr_assign_inputs
    sw_claim_transition_if_d  = sw_claim_transition_if_q;
    tap_claim_transition_if_d = tap_claim_transition_if_q;
    transition_token_d        = transition_token_q;
    transition_target_d       = transition_target_q;
    transition_cmd            = 1'b0;

    // SW mutex claim.
    if (tap_claim_transition_if_q != 8'hA5 &&
        reg2hw.claim_transition_if.qe) begin
      sw_claim_transition_if_d = reg2hw.claim_transition_if.q;
    end
    // TAP mutex claim. This has prio over SW above.
    if (sw_claim_transition_if_q != 8'hA5 &&
        tap_reg2hw.claim_transition_if.qe) begin
      tap_claim_transition_if_d = tap_reg2hw.claim_transition_if.q;
    end

    // The idle signal serves as the REGWEN in this case.
    if (lc_idle_d) begin
      if (tap_claim_transition_if_q == 8'hA5) begin
        transition_cmd = tap_reg2hw.transition_cmd.q &
                         tap_reg2hw.transition_cmd.qe;

        for (int k = 0; k < LcTokenWidth/32; k++) begin
          if (tap_reg2hw.transition_token[k].qe) begin
            transition_token_d[k*32 +: 32] = tap_reg2hw.transition_token[k].q;
          end
        end

        if (tap_reg2hw.transition_target.qe) begin
          transition_target_d = dec_lc_state_e'(tap_reg2hw.transition_target.q);
        end
      end else if (sw_claim_transition_if_q == 8'hA5) begin
        transition_cmd = reg2hw.transition_cmd.q &
                         reg2hw.transition_cmd.qe;

        for (int k = 0; k < LcTokenWidth/32; k++) begin
          if (reg2hw.transition_token[k].qe) begin
            transition_token_d[k*32 +: 32] = reg2hw.transition_token[k].q;
          end
        end

        if (reg2hw.transition_target.qe) begin
          transition_target_d = dec_lc_state_e'(reg2hw.transition_target.q);
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_csrs
    if (!rst_ni) begin
      trans_success_q           <= 1'b0;
      trans_cnt_oflw_error_q    <= 1'b0;
      trans_invalid_error_q     <= 1'b0;
      token_invalid_error_q     <= 1'b0;
      flash_rma_error_q         <= 1'b0;
      fatal_prog_error_q        <= 1'b0;
      fatal_state_error_q       <= 1'b0;
      sw_claim_transition_if_q  <= '0;
      tap_claim_transition_if_q <= '0;
      transition_token_q        <= '0;
      transition_target_q       <= DecLcStRaw;
      otp_part_error_q          <= '0;
    end else begin
      // All status and error bits are terminal and require a reset cycle.
      trans_success_q           <= trans_success_d        | trans_success_q;
      trans_cnt_oflw_error_q    <= trans_cnt_oflw_error_d | trans_cnt_oflw_error_q;
      trans_invalid_error_q     <= trans_invalid_error_d  | trans_invalid_error_q;
      token_invalid_error_q     <= token_invalid_error_d  | token_invalid_error_q;
      flash_rma_error_q         <= flash_rma_error_d      | flash_rma_error_q;
      fatal_prog_error_q        <= otp_prog_error_d       | fatal_prog_error_q;
      fatal_state_error_q       <= state_invalid_error_d  | fatal_state_error_q;
      otp_part_error_q          <= otp_lc_data_i.error    | otp_part_error_q;
      // Other regs, gated by mutex further below.
      sw_claim_transition_if_q  <= sw_claim_transition_if_d;
      tap_claim_transition_if_q <= tap_claim_transition_if_d;
      transition_token_q        <= transition_token_d;
      transition_target_q       <= transition_target_d;
    end
  end

  assign lc_flash_rma_seed_o = transition_token_q[RmaSeedWidth-1:0];

  //////////////////
  // Alert Sender //
  //////////////////

  logic [NumAlerts-1:0] alerts;
  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] tap_alert_test;

  assign alerts = {
    fatal_state_error_q,
    fatal_prog_error_q
  };

  assign alert_test = {
    reg2hw.alert_test.fatal_state_error.q &
    reg2hw.alert_test.fatal_state_error.qe,
    reg2hw.alert_test.fatal_prog_error.q &
    reg2hw.alert_test.fatal_prog_error.qe
  };

   assign tap_alert_test = {
    tap_reg2hw.alert_test.fatal_state_error.q &
    tap_reg2hw.alert_test.fatal_state_error.qe,
    tap_reg2hw.alert_test.fatal_prog_error.q &
    tap_reg2hw.alert_test.fatal_prog_error.qe
  };

  for (genvar k = 0; k < NumAlerts; k++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[k]),
      .IsFatal(1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[k] |
                       tap_alert_test[k] ),
      .alert_req_i   ( alerts[k]         ),
      .alert_ack_o   (                   ),
      .alert_state_o (                   ),
      .alert_rx_i    ( alert_rx_i[k]     ),
      .alert_tx_o    ( alert_tx_o[k]     )
    );
  end

  //////////////////////////
  // Escalation Receivers //
  //////////////////////////

  // This escalation action triggers the
  // lc_escalate_en life cycle control signal.
  logic esc_wipe_secrets;
  prim_esc_receiver u_prim_esc_receiver1 (
    .clk_i,
    .rst_ni,
    .esc_en_o (esc_wipe_secrets),
    .esc_rx_o (esc_wipe_secrets_rx_o),
    .esc_tx_i (esc_wipe_secrets_tx_i)
  );

  // This escalation action moves the life cycle
  // state into a temporary "SCRAP" state named "ESCALATE".
  logic esc_scrap_state;
  prim_esc_receiver u_prim_esc_receiver2 (
    .clk_i,
    .rst_ni,
    .esc_en_o (esc_scrap_state),
    .esc_rx_o (esc_scrap_state_rx_o),
    .esc_tx_i (esc_scrap_state_tx_i)
  );

  ////////////////////////////
  // Synchronization of IOs //
  ////////////////////////////

  // Signals going to and coming from power manager.
  logic lc_init;
  prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync_init (
    .clk_i,
    .rst_ni,
    .d_i(pwr_lc_i.lc_init),
    .q_o(lc_init)
  );

  logic lc_done_d, lc_done_q;
  logic lc_idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_sync_regs
    if (!rst_ni) begin
      lc_done_q <= 1'b0;
      lc_idle_q <= 1'b0;
    end else begin
      lc_done_q <= lc_done_d;
      lc_idle_q <= lc_idle_d;
    end
  end

  assign pwr_lc_o.lc_done = lc_done_q;
  assign pwr_lc_o.lc_idle = lc_idle_q;

  ////////////////////
  // KMAC Interface //
  ////////////////////

  logic token_hash_req, token_hash_ack, token_hash_err;
  lc_token_t hashed_token;
  lc_ctrl_kmac_if u_lc_ctrl_kmac_if (
    .clk_i,
    .rst_ni,
    .clk_kmac_i,
    .rst_kmac_ni,
    .kmac_data_i,
    .kmac_data_o,
    .transition_token_i ( transition_token_q ),
    .token_hash_req_i   ( token_hash_req     ),
    .token_hash_ack_o   ( token_hash_ack     ),
    .token_hash_err_o   ( token_hash_err     ),
    .hashed_token_o     ( hashed_token       )
  );

  ////////////
  // LC FSM //
  ////////////

  lc_ctrl_fsm #(
    .RndCnstLcKeymgrDivInvalid    ( RndCnstLcKeymgrDivInvalid    ),
    .RndCnstLcKeymgrDivTestDevRma ( RndCnstLcKeymgrDivTestDevRma ),
    .RndCnstLcKeymgrDivProduction ( RndCnstLcKeymgrDivProduction )
  ) u_lc_ctrl_fsm (
    .clk_i,
    .rst_ni,
    .init_req_i             ( lc_init                         ),
    .init_done_o            ( lc_done_d                       ),
    .idle_o                 ( lc_idle_d                       ),
    .esc_scrap_state_i      ( esc_scrap_state                 ),
    .esc_wipe_secrets_i     ( esc_wipe_secrets                ),
    .lc_state_valid_i       ( otp_lc_data_i.valid             ),
    .lc_state_i             ( otp_lc_data_i.state             ),
    .lc_id_state_i          ( otp_lc_data_i.id_state          ),
    .lc_cnt_i               ( otp_lc_data_i.count             ),
    .test_unlock_token_i    ( otp_lc_data_i.test_unlock_token ),
    .test_exit_token_i      ( otp_lc_data_i.test_exit_token   ),
    .rma_token_i            ( otp_lc_data_i.rma_token         ),
    .trans_cmd_i            ( transition_cmd                  ),
    .trans_target_i         ( transition_target_q             ),
    .dec_lc_state_o         ( dec_lc_state                    ),
    .dec_lc_cnt_o           ( dec_lc_cnt                      ),
    .dec_lc_id_state_o      ( dec_lc_id_state                 ),
    .token_hash_req_o       ( token_hash_req                  ),
    .token_hash_ack_i       ( token_hash_ack                  ),
    .token_hash_err_i       ( token_hash_err                  ),
    .hashed_token_i         ( hashed_token                    ),
    .otp_prog_req_o         ( lc_otp_program_o.req            ),
    .otp_prog_lc_state_o    ( lc_otp_program_o.state          ),
    .otp_prog_lc_cnt_o      ( lc_otp_program_o.count          ),
    .otp_prog_ack_i         ( lc_otp_program_i.ack            ),
    .otp_prog_err_i         ( lc_otp_program_i.err            ),
    .trans_success_o        ( trans_success_d                 ),
    .trans_cnt_oflw_error_o ( trans_cnt_oflw_error_d          ),
    .trans_invalid_error_o  ( trans_invalid_error_d           ),
    .token_invalid_error_o  ( token_invalid_error_d           ),
    .flash_rma_error_o      ( flash_rma_error_d               ),
    .otp_prog_error_o       ( otp_prog_error_d                ),
    .state_invalid_error_o  ( state_invalid_error_d           ),
    .lc_dft_en_o,
    .lc_nvm_debug_en_o,
    .lc_hw_debug_en_o,
    .lc_cpu_en_o,
    .lc_creator_seed_sw_rw_en_o,
    .lc_owner_seed_sw_rw_en_o,
    .lc_iso_part_sw_rd_en_o,
    .lc_iso_part_sw_wr_en_o,
    .lc_seed_hw_rd_en_o,
    .lc_keymgr_en_o,
    .lc_escalate_en_o,
    .lc_check_byp_en_o,
    .lc_clk_byp_req_o,
    .lc_clk_byp_ack_i,
    .lc_flash_rma_req_o,
    .lc_flash_rma_ack_i,
    .lc_keymgr_div_o
  );

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlOKnown,               tl_o                       )
  `ASSERT_KNOWN(AlertTxKnown_A,         alert_tx_o                 )
  `ASSERT_KNOWN(PwrLcKnown_A,           pwr_lc_o                   )
  `ASSERT_KNOWN(LcOtpProgramKnown_A,    lc_otp_program_o           )
  `ASSERT_KNOWN(LcOtpTokenKnown_A,      kmac_data_o                )
  `ASSERT_KNOWN(LcDftEnKnown_A,         lc_dft_en_o                )
  `ASSERT_KNOWN(LcNvmDebugEnKnown_A,    lc_nvm_debug_en_o          )
  `ASSERT_KNOWN(LcHwDebugEnKnown_A,     lc_hw_debug_en_o           )
  `ASSERT_KNOWN(LcCpuEnKnown_A,         lc_cpu_en_o                )
  `ASSERT_KNOWN(LcCreatorSwRwEn_A,      lc_creator_seed_sw_rw_en_o )
  `ASSERT_KNOWN(LcOwnerSwRwEn_A,        lc_owner_seed_sw_rw_en_o   )
  `ASSERT_KNOWN(LcIsoSwRwEn_A,          lc_iso_part_sw_rd_en_o     )
  `ASSERT_KNOWN(LcIsoSwWrEn_A,          lc_iso_part_sw_wr_en_o     )
  `ASSERT_KNOWN(LcSeedHwRdEn_A,         lc_seed_hw_rd_en_o         )
  `ASSERT_KNOWN(LcKeymgrEnKnown_A,      lc_keymgr_en_o             )
  `ASSERT_KNOWN(LcEscalateEnKnown_A,    lc_escalate_en_o           )
  `ASSERT_KNOWN(LcCheckBypassEnKnown_A, lc_check_byp_en_o          )
  `ASSERT_KNOWN(LcClkBypReqKnown_A,     lc_clk_byp_req_o           )
  `ASSERT_KNOWN(LcFlashRmaSeedKnown_A,  lc_flash_rma_seed_o        )
  `ASSERT_KNOWN(LcFlashRmaReqKnown_A,   lc_flash_rma_req_o         )
  `ASSERT_KNOWN(LcKeymgrDiv_A,          lc_keymgr_div_o            )

endmodule : lc_ctrl
