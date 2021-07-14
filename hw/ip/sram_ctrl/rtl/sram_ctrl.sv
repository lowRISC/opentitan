// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SRAM controller.
//

`include "prim_assert.sv"

module sram_ctrl
  import sram_ctrl_pkg::*;
  import sram_ctrl_reg_pkg::*;
#(
  // Number of words stored in the SRAM.
  parameter int MemSizeRam = 32'h1000,
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0] AlertAsyncOn          = {NumAlerts{1'b1}},
  // Enables the execute from SRAM feature.
  parameter bit InstrExec                               = 1,
  // Random netlist constants
  parameter otp_ctrl_pkg::sram_key_t   RndCnstSramKey   = RndCnstSramKeyDefault,
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramNonce = RndCnstSramNonceDefault,
  parameter lfsr_perm_t                RndCnstSramLfsrPerm = RndCnstSramLfsrPermDefault
) (
  // SRAM Clock
  input  logic                                       clk_i,
  input  logic                                       rst_ni,
  // OTP Clock (for key interface)
  input  logic                                       clk_otp_i,
  input  logic                                       rst_otp_ni,
  // Bus Interface (device) for SRAM
  input  tlul_pkg::tl_h2d_t                          ram_tl_i,
  output tlul_pkg::tl_d2h_t                          ram_tl_o,
  // Bus Interface (device) for CSRs
  input  tlul_pkg::tl_h2d_t                          regs_tl_i,
  output tlul_pkg::tl_d2h_t                          regs_tl_o,
  // Alert outputs.
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]  alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]  alert_tx_o,
  // Life-cycle escalation input (scraps the scrambling keys)
  input  lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t                        lc_hw_debug_en_i,
  // Otp configuration for sram execution
  input  otp_ctrl_pkg::otp_en_t                      otp_en_sram_ifetch_i,
  // Key request to OTP (running on clk_fixed)
  output otp_ctrl_pkg::sram_otp_key_req_t            sram_otp_key_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t            sram_otp_key_i,
  // config
  input  prim_ram_1p_pkg::ram_1p_cfg_t               cfg_i
);

  // This is later on pruned to the correct width at the SRAM wrapper interface.
  parameter int Depth = MemSizeRam >> 2;
  parameter int AddrWidth = prim_util_pkg::vbits(Depth);

  // This peripheral only works up to a width of 64bits.
  `ASSERT_INIT(WidthMustBeBelow64_A, DataWidth <= 64)
  `ASSERT_INIT(NonceWidthsLessThanSource_A,
      NonceWidth + RandInitSeed <= otp_ctrl_pkg::SramNonceWidth)

  //////////////////////////
  // CSR Node and Mapping //
  //////////////////////////

  sram_ctrl_regs_reg2hw_t reg2hw;
  sram_ctrl_regs_hw2reg_t hw2reg;

  sram_ctrl_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_i),
    .tl_o      (regs_tl_o),
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i (1'b1)
   );

  // Key and attribute outputs to scrambling device
  logic [otp_ctrl_pkg::SramKeyWidth-1:0]   key_d, key_q;
  logic [otp_ctrl_pkg::SramNonceWidth-1:0] nonce_d, nonce_q;

  // tie-off unused nonce bits
  if (otp_ctrl_pkg::SramNonceWidth > NonceWidth) begin : gen_nonce_tieoff
    logic unused_nonce;
    assign unused_nonce = ^nonce_q[otp_ctrl_pkg::SramNonceWidth-1:NonceWidth];
  end


  // Status register outputs
  logic parity_error_d, parity_error_q;
  logic escalated_q;
  logic key_valid_d, key_valid_q;
  logic key_seed_valid_d, key_seed_valid_q;
  assign hw2reg.status.error              = parity_error_q;
  assign hw2reg.status.escalated.d        = escalated_q;
  assign hw2reg.status.scr_key_valid      = key_valid_q;
  assign hw2reg.status.scr_key_seed_valid = key_seed_valid_q;

  // Control register
  logic key_req;
  assign key_req = reg2hw.ctrl.renew_scr_key.q & reg2hw.ctrl.renew_scr_key.qe;

  // Parity error (the error is sticky and cannot be cleared).
  logic [1:0]  sram_rerror;
  logic [31:0] sram_rerror_addr;
  assign hw2reg.error_address.d             = sram_rerror_addr;
  assign hw2reg.error_address.de            = sram_rerror[1];
  assign parity_error_d                     = parity_error_q | sram_rerror[1];

  // Correctable RAM errors are not supported
  logic unused_error;
  assign unused_error = sram_rerror[0];

  // Parameter not used within module
  // The memory is the user of the perm parameter.  At the moment memories are not instantianted
  // inside sram_ctrl but parallel to it.
  lfsr_perm_t unused_perm_param;
  assign unused_perm_param = RndCnstSramLfsrPerm;


  //////////////////
  // Alert Sender //
  //////////////////

  logic intg_error;
  logic [NumAlerts-1:0] alert, alert_test;

  assign alert = {
                   parity_error_q,
                   intg_error
                 };


  assign alert_test = {
                        reg2hw.alert_test.fatal_parity_error.q &
                        reg2hw.alert_test.fatal_parity_error.qe,
                        reg2hw.alert_test.fatal_intg_error.q &
                        reg2hw.alert_test.fatal_intg_error.qe
                      };

  for (genvar i=0; i < NumAlerts; i++) begin : gen_alerts
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1)
    ) u_prim_alert_sender_parity (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end


  //////////////////////////////////////////
  // Lifecycle Escalation Synchronization //
  //////////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t escalate_en;
  prim_lc_sync #(
    .NumCopies (1)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i (lc_escalate_en_i),
    .lc_en_o (escalate_en)
  );

  ////////////////////////////
  // Scrambling Key Request //
  ////////////////////////////

  // The scrambling key and nonce have to be requested from the OTP controller via a req/ack
  // protocol. Since the OTP controller works in a different clock domain, we have to synchronize
  // the req/ack protocol as described in more details here:
  // https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#interfaces-to-sram-and-otbn-scramblers
  logic key_ack;
  logic key_req_pending_d, key_req_pending_q;
  assign key_req_pending_d = (key_req) ? 1'b1 :
                             (key_ack) ? 1'b0 : key_req_pending_q;

  logic init_q;
  logic init_ack;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      init_q <= '0;
    end else if (init_q && init_ack) begin
      init_q <= '0;
    end else if (reg2hw.ctrl.init.q && reg2hw.ctrl.init.qe) begin
      init_q <= 1'b1;
    end
  end

  assign hw2reg.ctrl.renew_scr_key.d = '0;
  assign hw2reg.ctrl.init.d = init_q;

  // The SRAM scrambling wrapper will not accept any transactions while
  // the key req is pending or if we have escalated.
  // Note that we're not using key_valid_q here, such that the SRAM can be used
  // right after reset, where the keys are reset to the default netlist constant.
  logic key_valid;
  assign key_valid = ~(key_req_pending_q | escalated_q);

  logic init_req;
  assign init_req  = init_q & key_valid_q;

  assign key_valid_d       = (key_req) ? 1'b0 :
                             (key_ack) ? 1'b1 : key_valid_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      key_req_pending_q <= 1'b0;
      key_valid_q       <= 1'b0;
      key_seed_valid_q  <= 1'b0;
      parity_error_q    <= 1'b0;
      escalated_q       <= 1'b0;
      key_q             <= RndCnstSramKey;
      nonce_q           <= RndCnstSramNonce;
    end else begin
      key_req_pending_q <= key_req_pending_d;
      key_valid_q       <= key_valid_d;
      parity_error_q    <= parity_error_d;
      if (key_ack) begin
        key_seed_valid_q  <= key_seed_valid_d;
        key_q             <= key_d;
        nonce_q           <= nonce_d;
      end
      // This scraps the keys.
      if (escalate_en != lc_ctrl_pkg::Off || escalated_q) begin
        escalated_q       <= 1'b1;
        key_seed_valid_q  <= 1'b0;
        key_q             <= RndCnstSramKey;
        nonce_q           <= RndCnstSramNonce;
      end
    end
  end

  prim_sync_reqack_data #(
    .Width($bits(otp_ctrl_pkg::sram_otp_key_rsp_t)-1),
    .DataSrc2Dst(1'b0)
  ) u_prim_sync_reqack_data (
    .clk_src_i  ( clk_i              ),
    .rst_src_ni ( rst_ni             ),
    .clk_dst_i  ( clk_otp_i          ),
    .rst_dst_ni ( rst_otp_ni         ),
    .src_req_i  ( key_req_pending_q  ),
    .src_ack_o  ( key_ack            ),
    .dst_req_o  ( sram_otp_key_o.req ),
    .dst_ack_i  ( sram_otp_key_i.ack ),
    .data_i     ( {sram_otp_key_i.key,
                   sram_otp_key_i.nonce,
                   sram_otp_key_i.seed_valid} ),
    .data_o     ( {key_d,
                   nonce_d,
                   key_seed_valid_d}          )
  );

  ////////////////////
  // SRAM Execution //
  ////////////////////

  tlul_pkg::tl_instr_en_e en_ifetch;
  if (InstrExec) begin : gen_instr_ctrl
    tlul_pkg::tl_instr_en_e lc_ifetch_en;
    tlul_pkg::tl_instr_en_e reg_ifetch_en;
    assign lc_ifetch_en = (lc_hw_debug_en_i == lc_ctrl_pkg::On) ? tlul_pkg::InstrEn :
                                                                  tlul_pkg::InstrDis;
    assign reg_ifetch_en = tlul_pkg::tl_instr_en_e'(reg2hw.exec.q);
    assign en_ifetch = (otp_en_sram_ifetch_i == otp_ctrl_pkg::Enabled) ? reg_ifetch_en :
                                                                         lc_ifetch_en;
  end else begin : gen_tieoff
    assign en_ifetch = tlul_pkg::InstrDis;

    // tie off unused signals
    logic unused_sigs;
    assign unused_sigs = ^{lc_hw_debug_en_i,
                           reg2hw.exec.q};
  end

  /////////////////////////////////
  // SRAM with scrambling device //
  /////////////////////////////////

  logic sram_intg_error;
  logic sram_req, sram_gnt, sram_we, sram_rvalid;
  logic [AddrWidth-1:0] sram_addr;
  logic [DataWidth-1:0] sram_wdata, sram_wmask, sram_rdata;

  tlul_adapter_sram #(
    .SramAw(AddrWidth),
    .SramDw(DataWidth - tlul_pkg::DataIntgWidth),
    .Outstanding(2),
    .ByteAccess(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1)
  ) u_tl_adapter_ram_main (
    .clk_i,
    .rst_ni,
    .tl_i        (ram_tl_i),
    .tl_o        (ram_tl_o),
    .en_ifetch_i (en_ifetch),
    .req_o       (sram_req),
    .req_type_o  (),
    .gnt_i       (sram_gnt),
    .we_o        (sram_we),
    .addr_o      (sram_addr),
    .wdata_o     (sram_wdata),
    .wmask_o     (sram_wmask),
    .intg_error_o(sram_intg_error),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    (sram_rerror)
  );

  prim_ram_1p_scr #(
    .Width(DataWidth),
    .Depth(Depth),
    .LfsrWidth(RandInitSeed),
    .EnableParity(0),
    .StatePerm(RndCnstSramLfsrPerm),
    .DataBitsPerMask(DataWidth),
    .DiffWidth(DataWidth)
  ) u_prim_ram_1p_scr (
    .clk_i,
    .rst_ni,

    .key_valid_i (key_valid),
    .key_i       (key_q),
    .nonce_i     (nonce_q[NonceWidth-1:0]),
    .init_req_i  (init_req),
    .init_seed_i (nonce_q[NonceWidth +: RandInitSeed]),
    .init_ack_o  (init_ack),

    .req_i       (sram_req),
    .intg_error_i(sram_intg_error),
    .gnt_o       (sram_gnt),
    .write_i     (sram_we),
    .addr_i      (sram_addr),
    .wdata_i     (sram_wdata),
    .wmask_i     (sram_wmask),
    .rdata_o     (sram_rdata),
    .rvalid_o    (sram_rvalid),
    .rerror_o    (sram_rerror),
    .raddr_o     (sram_rerror_addr),
    .intg_error_o(intg_error),
    .cfg_i
  );

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(RegsTlOutKnown_A,  regs_tl_o)
  `ASSERT_KNOWN(RamTlOutKnown_A,   ram_tl_o)
  `ASSERT_KNOWN(AlertOutKnown_A,   alert_tx_o)
  `ASSERT_KNOWN(SramOtpKeyKnown_A, sram_otp_key_o)

endmodule : sram_ctrl
