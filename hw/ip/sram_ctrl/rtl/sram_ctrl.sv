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
  parameter lfsr_seed_t                RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t                RndCnstLfsrPerm  = RndCnstLfsrPermDefault
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
  input  prim_mubi_pkg::mubi8_t                      otp_en_sram_ifetch_i,
  // Key request to OTP (running on clk_fixed)
  output otp_ctrl_pkg::sram_otp_key_req_t            sram_otp_key_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t            sram_otp_key_i,
  // config
  input  prim_ram_1p_pkg::ram_1p_cfg_t               cfg_i
);

  // This is later on pruned to the correct width at the SRAM wrapper interface.
  parameter int unsigned Depth = MemSizeRam >> 2;
  parameter int unsigned AddrWidth = prim_util_pkg::vbits(Depth);

  `ASSERT_INIT(NonceWidthsLessThanSource_A, NonceWidth + LfsrWidth <= otp_ctrl_pkg::SramNonceWidth)

  //////////////////////////
  // CSR Node and Mapping //
  //////////////////////////

  // We've got two bus interfaces in this module, hence two integ failure sources.
  logic [1:0] bus_integ_error;

  sram_ctrl_regs_reg2hw_t reg2hw;
  sram_ctrl_regs_hw2reg_t hw2reg;

  sram_ctrl_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_i),
    .tl_o      (regs_tl_o),
    .reg2hw,
    .hw2reg,
    .intg_err_o(bus_integ_error[0]),
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

  //////////////////
  // Alert Sender //
  //////////////////

  logic alert_test;
  assign alert_test = reg2hw.alert_test.q & reg2hw.alert_test.qe;

  assign hw2reg.status.bus_integ_error.d  = 1'b1;
  assign hw2reg.status.bus_integ_error.de = |bus_integ_error;

  logic init_error;
  assign hw2reg.status.init_error.d  = 1'b1;
  assign hw2reg.status.init_error.de = init_error;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .IsFatal(1)
  ) u_prim_alert_sender_parity (
    .clk_i,
    .rst_ni,
    .alert_test_i  ( alert_test                    ),
    .alert_req_i   ( |bus_integ_error | init_error ),
    .alert_ack_o   (                               ),
    .alert_state_o (                               ),
    .alert_rx_i    ( alert_rx_i[0]                 ),
    .alert_tx_o    ( alert_tx_o[0]                 )
  );

  /////////////////////////
  // Escalation Triggers //
  /////////////////////////

  lc_ctrl_pkg::lc_tx_t escalate_en;
  prim_lc_sync #(
    .NumCopies (1)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i (lc_escalate_en_i),
    .lc_en_o (escalate_en)
  );

  logic escalate;
  assign escalate = (escalate_en != lc_ctrl_pkg::Off);
  assign hw2reg.status.escalated.d  = 1'b1;
  assign hw2reg.status.escalated.de = escalate;

  // Aggregate external and internal escalation sources. This is used on countermeasures further
  // below (key reset, transaction blocking and scrambling nonce reversal).
  logic local_esc;
  assign local_esc = escalate                   |
                     init_error                 |
                     |bus_integ_error           |
                     reg2hw.status.escalated.q  |
                     reg2hw.status.init_error.q |
                     reg2hw.status.bus_integ_error.q;

  ///////////////////////
  // HW Initialization //
  ///////////////////////

  // A write to the init register reloads the LFSR seed, resets the init counter and
  // sets init_q to flag a pending initialization request.
  logic init_trig;
  assign init_trig = reg2hw.ctrl.init.q & reg2hw.ctrl.init.qe;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // we trigger an alert.
  logic [1:0] init_req, init_done, init_q;
  logic [1:0][AddrWidth-1:0] init_cnt_q;
  for (genvar k = 0; k < 2; k++) begin : gen_double_cnt

    // These size_only buffers are instantiated in order to prevent
    // optimization / merging of the two counters.
    logic init_trig_buf;
    prim_buf u_prim_buf_trig (
      .in_i(init_trig),
      .out_o(init_trig_buf)
    );

    // This waits until the scrambling keys are actually valid (this allows the SW to trigger
    // key renewal and initialization at the same time).
    assign init_req[k]  = init_q[k] & reg2hw.status.scr_key_valid.q;
    assign init_done[k] = (init_cnt_q[k] == AddrWidth'(Depth - 1)) & init_req[k];

    logic init_d;
    assign init_d     = (init_done[k])  ? 1'b0 :
                        (init_trig_buf) ? 1'b1 : init_q[k];

    logic [AddrWidth-1:0] init_cnt_d;
    assign init_cnt_d = (init_trig_buf) ? '0                   :
                        (init_req[k])   ? init_cnt_q[k] + 1'b1 : init_cnt_q[k];

    prim_flop #(
      .Width(1+AddrWidth)
    ) u_prim_flop_cnt (
      .clk_i,
      .rst_ni,
      .d_i({init_d, init_cnt_d}),
      .q_o({init_q[k], init_cnt_q[k]})
    );
  end

  // Clear this bit on local escalation.
  assign hw2reg.status.init_done.d  = init_done[0] & ~init_trig & ~local_esc;
  assign hw2reg.status.init_done.de = init_done[0] | init_trig | local_esc;

  // Check whether counter is glitched into an invalid state
  assign init_error = {init_q[0], init_cnt_q[0]} !=
                      {init_q[1], init_cnt_q[1]};

  ////////////////////////////
  // Scrambling Key Request //
  ////////////////////////////

  // The scrambling key and nonce have to be requested from the OTP controller via a req/ack
  // protocol. Since the OTP controller works in a different clock domain, we have to synchronize
  // the req/ack protocol as described in more details here:
  // https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#interfaces-to-sram-and-otbn-scramblers
  logic key_req, key_ack;
  logic key_req_pending_d, key_req_pending_q;
  assign key_req = reg2hw.ctrl.renew_scr_key.q & reg2hw.ctrl.renew_scr_key.qe;
  assign key_req_pending_d = (key_req) ? 1'b1 :
                             (key_ack) ? 1'b0 : key_req_pending_q;

  // The SRAM scrambling wrapper will not accept any transactions while
  // the key req is pending or if we have escalated.
  // Note that we're not using key_valid_q here, such that the SRAM can be used
  // right after reset, where the keys are reset to the default netlist constant.
  logic key_valid;
  assign key_valid = ~(key_req_pending_q | reg2hw.status.escalated.q);

  // Clear this bit on local escalation.
  assign hw2reg.status.scr_key_valid.d   = key_ack & ~key_req & ~local_esc;
  assign hw2reg.status.scr_key_valid.de  = key_req | key_ack | local_esc;

  // Clear this bit on local escalation.
  logic key_seed_valid;
  assign hw2reg.status.scr_key_seed_valid.d  = key_seed_valid & ~local_esc;
  assign hw2reg.status.scr_key_seed_valid.de = key_ack | local_esc;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      key_req_pending_q <= 1'b0;
      key_q             <= RndCnstSramKey;
      nonce_q           <= RndCnstSramNonce;
    end else begin
      key_req_pending_q <= key_req_pending_d;
      if (key_ack) begin
        key_q   <= key_d;
        nonce_q <= nonce_d;
      end
      // This scraps the keys.
      if (local_esc) begin
        key_q   <= RndCnstSramKey;
        nonce_q <= RndCnstSramNonce;
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
    .req_chk_i  ( 1'b1               ),
    .src_req_i  ( key_req_pending_q  ),
    .src_ack_o  ( key_ack            ),
    .dst_req_o  ( sram_otp_key_o.req ),
    .dst_ack_i  ( sram_otp_key_i.ack ),
    .data_i     ( {sram_otp_key_i.key,
                   sram_otp_key_i.nonce,
                   sram_otp_key_i.seed_valid} ),
    .data_o     ( {key_d,
                   nonce_d,
                   key_seed_valid}          )
  );

  logic unused_csr_sigs;
  assign unused_csr_sigs = ^{reg2hw.status.init_done.q,
                             reg2hw.status.scr_key_seed_valid.q};

  ////////////////////
  // SRAM Execution //
  ////////////////////

  import prim_mubi_pkg::mubi4_e;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi8_test_true_strict;

  mubi4_e en_ifetch;
  if (InstrExec) begin : gen_instr_ctrl
    mubi4_e lc_ifetch_en;
    mubi4_e reg_ifetch_en;
    assign lc_ifetch_en = (lc_hw_debug_en_i == lc_ctrl_pkg::On) ? MuBi4True :
                                                                  MuBi4False;
    assign reg_ifetch_en = mubi4_e'(reg2hw.exec.q);
    assign en_ifetch = (mubi8_test_true_strict(otp_en_sram_ifetch_i)) ? reg_ifetch_en :
                                                                        lc_ifetch_en;
  end else begin : gen_tieoff
    assign en_ifetch = MuBi4False;

    // tie off unused signals
    logic unused_sigs;
    assign unused_sigs = ^{lc_hw_debug_en_i,
                           reg2hw.exec.q,
                           otp_en_sram_ifetch_i};
  end

  /////////////////////////
  // Initialization LFSR //
  /////////////////////////

  logic [LfsrWidth-1:0] lfsr_out;
  prim_lfsr #(
    .LfsrDw      ( LfsrWidth       ),
    .EntropyDw   ( LfsrWidth       ),
    .StateOutDw  ( LfsrWidth       ),
    .DefaultSeed ( RndCnstLfsrSeed ),
    .StatePermEn ( 1'b1            ),
    .StatePerm   ( RndCnstLfsrPerm )
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .lfsr_en_i(init_req[0]),
    .seed_en_i(init_trig),
    .seed_i(nonce_q[NonceWidth +: LfsrWidth]),
    .entropy_i('0),
    .state_o(lfsr_out)
  );

  // Compute the correct integrity alongside for the pseudo-random initialization values.
  logic [DataWidth - 1 :0] lfsr_out_integ;
  tlul_data_integ_enc u_tlul_data_integ_enc (
    .data_i(lfsr_out),
    .data_intg_o(lfsr_out_integ)
  );

  /////////////////////////////////
  // SRAM with scrambling device //
  /////////////////////////////////

  logic tlul_req, tlul_gnt, tlul_we;
  logic [AddrWidth-1:0] tlul_addr;
  logic [DataWidth-1:0] tlul_wdata, tlul_wmask;

  logic sram_intg_error, sram_req, sram_gnt, sram_we, sram_rvalid;
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
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i        (ram_tl_i),
    .tl_o        (ram_tl_o),
    .en_ifetch_i (en_ifetch),
    .req_o       (tlul_req),
    .req_type_o  (),
    .gnt_i       (tlul_gnt),
    .we_o        (tlul_we),
    .addr_o      (tlul_addr),
    .wdata_o     (tlul_wdata),
    .wmask_o     (tlul_wmask),
    .intg_error_o(bus_integ_error[1]),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    ('0)
  );

  // Interposing mux logic for initialization with pseudo random data.
  assign sram_req        = tlul_req | init_req[0];
  assign tlul_gnt        = sram_gnt & ~init_req[0];
  assign sram_we         = tlul_we | init_req[0];
  assign sram_intg_error = local_esc & ~init_req[0];
  assign sram_addr       = (init_req[0]) ? init_cnt_q[0]     : tlul_addr;
  assign sram_wdata      = (init_req[0]) ? lfsr_out_integ    : tlul_wdata;
  assign sram_wmask      = (init_req[0]) ? {DataWidth{1'b1}} : tlul_wmask;

  prim_ram_1p_scr #(
    .Width(DataWidth),
    .Depth(Depth),
    .EnableParity(0),
    .DataBitsPerMask(DataWidth),
    .DiffWidth(DataWidth)
  ) u_prim_ram_1p_scr (
    .clk_i,
    .rst_ni,

    .key_valid_i (key_valid),
    .key_i       (key_q),
    .nonce_i     (nonce_q[NonceWidth-1:0]),

    .req_i       (sram_req),
    .intg_error_i(sram_intg_error),
    .gnt_o       (sram_gnt),
    .write_i     (sram_we),
    .addr_i      (sram_addr),
    .wdata_i     (sram_wdata),
    .wmask_i     (sram_wmask),
    .rdata_o     (sram_rdata),
    .rvalid_o    (sram_rvalid),
    .rerror_o    ( ),
    .raddr_o     ( ),
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
