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
  // SEC_CM: LC_ESCALATE_EN.INTERSIG.MUBI
  input  lc_ctrl_pkg::lc_tx_t                        lc_escalate_en_i,
  // SEC_CM: LC_HW_DEBUG_EN.INTERSIG.MUBI
  input  lc_ctrl_pkg::lc_tx_t                        lc_hw_debug_en_i,
  // Otp configuration for sram execution
  // SEC_CM: EXEC.INTERSIG.MUBI
  input  prim_mubi_pkg::mubi8_t                      otp_en_sram_ifetch_i,
  // Key request to OTP (running on clk_fixed)
  // SEC_CM: SCRAMBLE.KEY.SIDELOAD
  output otp_ctrl_pkg::sram_otp_key_req_t            sram_otp_key_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t            sram_otp_key_i,
  // config
  input  prim_ram_1p_pkg::ram_1p_cfg_t               cfg_i
);

  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::lc_tx_test_true_loose;
  import lc_ctrl_pkg::lc_tx_bool_to_lc_tx;
  import lc_ctrl_pkg::lc_tx_or_hi;
  import lc_ctrl_pkg::lc_tx_inv;
  import lc_ctrl_pkg::lc_to_mubi4;

  // This is later on pruned to the correct width at the SRAM wrapper interface.
  parameter int unsigned Depth = MemSizeRam >> 2;
  parameter int unsigned AddrWidth = prim_util_pkg::vbits(Depth);

  `ASSERT_INIT(NonceWidthsLessThanSource_A, NonceWidth + LfsrWidth <= otp_ctrl_pkg::SramNonceWidth)


  /////////////////////////////////////
  // Anchor incoming seeds and constants
  /////////////////////////////////////
  localparam int TotalAnchorWidth = $bits(otp_ctrl_pkg::sram_key_t) +
                                    $bits(otp_ctrl_pkg::sram_nonce_t);

  otp_ctrl_pkg::sram_key_t cnst_sram_key;
  otp_ctrl_pkg::sram_nonce_t cnst_sram_nonce;

  prim_sec_anchor_buf #(
    .Width(TotalAnchorWidth)
  ) u_seed_anchor (
    .in_i({RndCnstSramKey,
           RndCnstSramNonce}),
    .out_o({cnst_sram_key,
            cnst_sram_nonce})
  );


  //////////////////////////
  // CSR Node and Mapping //
  //////////////////////////

  // We've got two bus interfaces + an lc_gate in this module,
  // hence three integ failure sources.
  logic [2:0] bus_integ_error;

  sram_ctrl_regs_reg2hw_t reg2hw;
  sram_ctrl_regs_hw2reg_t hw2reg;

  // SEC_CM: CTRL.CONFIG.REGWEN
  // SEC_CM: EXEC.CONFIG.REGWEN
  sram_ctrl_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_i),
    .tl_o      (regs_tl_o),
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
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

  logic alert_req;
  assign alert_req = (|bus_integ_error) | init_error;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .IsFatal(1)
  ) u_prim_alert_sender_parity (
    .clk_i,
    .rst_ni,
    .alert_test_i  ( alert_test    ),
    .alert_req_i   ( alert_req     ),
    .alert_ack_o   (               ),
    .alert_state_o (               ),
    .alert_rx_i    ( alert_rx_i[0] ),
    .alert_tx_o    ( alert_tx_o[0] )
  );

  /////////////////////////
  // Escalation Triggers //
  /////////////////////////

  lc_tx_t [1:0] escalate_en;
  prim_lc_sync #(
    .NumCopies (2)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i (lc_escalate_en_i),
    .lc_en_o (escalate_en)
  );

  // SEC_CM: KEY.GLOBAL_ESC
  logic escalate;
  assign escalate = lc_tx_test_true_loose(escalate_en[0]);
  assign hw2reg.status.escalated.d  = 1'b1;
  assign hw2reg.status.escalated.de = escalate;

  // SEC_CM: KEY.LOCAL_ESC
  // Aggregate external and internal escalation sources.
  // This is used in countermeasures further below (key reset and transaction blocking).
  logic local_esc, local_esc_reg;
  // This signal only aggregates registered escalation signals and is used for transaction
  // blocking further below, which is on a timing-critical path.
  assign local_esc_reg = reg2hw.status.escalated.q  |
                         reg2hw.status.init_error.q |
                         reg2hw.status.bus_integ_error.q;
  // This signal aggregates all escalation trigger signals, including the ones that are generated in
  // the same cycle such as init_error and bus_integ_error. It is used for countermeasures that are
  // not on the critical path (such as clearing the scrambling keys).
  assign local_esc = escalate           |
                     init_error         |
                     (|bus_integ_error) |
                     local_esc_reg;

  // Convert registered, local escalation sources to a multibit signal and combine this with
  // the incoming escalation enable signal before feeding into the TL-UL gate further below.
  lc_tx_t lc_tlul_gate_en;
  assign lc_tlul_gate_en = lc_tx_inv(lc_tx_or_hi(escalate_en[1],
                                                 lc_tx_bool_to_lc_tx(local_esc_reg)));
  ///////////////////////
  // HW Initialization //
  ///////////////////////

  // A write to the init register reloads the LFSR seed, resets the init counter and
  // sets init_q to flag a pending initialization request.
  logic init_trig;
  assign init_trig = reg2hw.ctrl.init.q & reg2hw.ctrl.init.qe;

  logic init_d, init_q, init_done;
  assign init_d = (init_done) ? 1'b0 :
                  (init_trig) ? 1'b1 : init_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_init_reg
    if(!rst_ni) begin
      init_q <= 1'b0;
    end else begin
      init_q <= init_d;
    end
  end

  // This waits until the scrambling keys are actually valid (this allows the SW to trigger
  // key renewal and initialization at the same time).
  logic init_req;
  logic [AddrWidth-1:0] init_cnt;
  logic key_req_pending_d, key_req_pending_q;
  assign init_req  = init_q & ~key_req_pending_q;
  assign init_done = (init_cnt == AddrWidth'(Depth - 1)) & init_req;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // we trigger an alert.
  // SEC_CM: INIT.CTR.REDUN
  prim_count #(
    .Width(AddrWidth)
  ) u_prim_count (
    .clk_i,
    .rst_ni,
    .clr_i(init_trig),
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(init_req),
    .decr_en_i(1'b0),
    .step_i(AddrWidth'(1)),
    .cnt_o(init_cnt),
    .cnt_next_o(),
    .err_o(init_error)
  );

  // Clear this bit on local escalation.
  assign hw2reg.status.init_done.d  = init_done & ~init_trig & ~local_esc;
  assign hw2reg.status.init_done.de = init_done | init_trig | local_esc;

  ////////////////////////////
  // Scrambling Key Request //
  ////////////////////////////

  // The scrambling key and nonce have to be requested from the OTP controller via a req/ack
  // protocol. Since the OTP controller works in a different clock domain, we have to synchronize
  // the req/ack protocol as described in more details here:
  // https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#interfaces-to-sram-and-otbn-scramblers
  logic key_req, key_ack;
  assign key_req = reg2hw.ctrl.renew_scr_key.q & reg2hw.ctrl.renew_scr_key.qe;
  assign key_req_pending_d = (key_req) ? 1'b1 :
                             (key_ack) ? 1'b0 : key_req_pending_q;

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
      // reset case does not use buffered values as the
      // reset value will be directly encoded into flop types
      key_q             <= RndCnstSramKey;
      nonce_q           <= RndCnstSramNonce;
    end else begin
      key_req_pending_q <= key_req_pending_d;
      if (key_ack) begin
        key_q   <= key_d;
        nonce_q <= nonce_d;
      end
      // This scraps the keys.
      // SEC_CM: KEY.GLOBAL_ESC
      // SEC_CM: KEY.LOCAL_ESC
      if (local_esc) begin
        key_q   <= cnst_sram_key;
        nonce_q <= cnst_sram_nonce;
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
                   key_seed_valid} )
  );

  logic unused_csr_sigs;
  assign unused_csr_sigs = ^{reg2hw.status.init_done.q,
                             reg2hw.status.scr_key_seed_valid.q};

  ////////////////////
  // SRAM Execution //
  ////////////////////

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi8_test_true_strict;

  mubi4_t en_ifetch;
  if (InstrExec) begin : gen_instr_ctrl
    mubi4_t lc_ifetch_en;
    mubi4_t reg_ifetch_en;
    // SEC_CM: INSTR.BUS.LC_GATED
    assign lc_ifetch_en = lc_to_mubi4(lc_hw_debug_en_i);
    // SEC_CM: EXEC.CONFIG.MUBI
    assign reg_ifetch_en = mubi4_t'(reg2hw.exec.q);
    // SEC_CM: EXEC.INTERSIG.MUBI
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
    .lfsr_en_i(init_req),
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

  ////////////////////////////
  // SRAM TL-UL Access Gate //
  ////////////////////////////

  logic tl_gate_resp_pending;
  tlul_pkg::tl_h2d_t ram_tl_in_gated;
  tlul_pkg::tl_d2h_t ram_tl_out_gated;

  // SEC_CM: RAM_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate #(
    .NumGatesPerDirection(2)
  ) u_tlul_lc_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(ram_tl_i),
    .tl_d2h_o(ram_tl_o),
    .tl_h2d_o(ram_tl_in_gated),
    .tl_d2h_i(ram_tl_out_gated),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o(tl_gate_resp_pending),
    .lc_en_i (lc_tlul_gate_en),
    .err_o   (bus_integ_error[2])
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
    .EnableDataIntgPt(1), // SEC_CM: MEM.INTEGRITY
    .SecFifoPtr      (1)  // SEC_CM: TLUL_FIFO.CTR.REDUN
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i        (ram_tl_in_gated),
    .tl_o        (ram_tl_out_gated),
    .en_ifetch_i (en_ifetch),
    .req_o       (tlul_req),
    .req_type_o  (),
    .gnt_i       (tlul_gnt),
    .we_o        (tlul_we),
    .addr_o      (tlul_addr),
    .wdata_o     (tlul_wdata),
    .wmask_o     (tlul_wmask),
    // SEC_CM: BUS.INTEGRITY
    .intg_error_o(bus_integ_error[1]),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    ('0)
  );

  // Interposing mux logic for initialization with pseudo random data.
  assign sram_req        = tlul_req | init_req;
  assign tlul_gnt        = sram_gnt & ~init_req;
  assign sram_we         = tlul_we | init_req;
  assign sram_intg_error = |bus_integ_error[2:1] & ~init_req;
  assign sram_addr       = (init_req) ? init_cnt          : tlul_addr;
  assign sram_wdata      = (init_req) ? lfsr_out_integ    : tlul_wdata;
  assign sram_wmask      = (init_req) ? {DataWidth{1'b1}} : tlul_wmask;

  // The SRAM scrambling wrapper will not accept any transactions while the
  // key req is pending or if we have escalated. Note that we're not using
  // the scr_key_valid CSR here, such that the SRAM can be used right after
  // reset, where the keys are reset to the default netlist constant.
  //
  // If we have escalated, but there is a pending request in the TL gate, we
  // may have a pending read-modify-write transaction in the SRAM adapter. In
  // that case we let a write proceed, since the TL gate won't accept any new
  // transactions and the SRAM keys have been clobbered already.
  logic key_valid;
  assign key_valid = (key_req_pending_q)         ? 1'b0 :
                     (reg2hw.status.escalated.q) ? (tl_gate_resp_pending & tlul_we) : 1'b1;

  // SEC_CM: MEM.SCRAMBLE, ADDR.SCRAMBLE
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
  `ASSERT_KNOWN(RamTlOutKnown_A,   ram_tl_o.d_valid)
  `ASSERT_KNOWN_IF(RamTlOutPayLoadKnown_A, ram_tl_o, ram_tl_o.d_valid)
  `ASSERT_KNOWN(AlertOutKnown_A,   alert_tx_o)
  `ASSERT_KNOWN(SramOtpKeyKnown_A, sram_otp_key_o)

  // Alert assertions for redundant counters.
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(CntCheck_A,
      u_prim_count, alert_tx_o[0])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(LcGateFsmCheck_A,
      u_tlul_lc_gate.u_state_regs, alert_tx_o[0])

  // Alert assertions for reg_we onehot check.
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A,
      u_reg_regs, alert_tx_o[0])

  // Alert assertions for redundant counters.
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(FifoWptrCheck_A,
      u_tlul_adapter_sram.u_rspfifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_wptr,
      alert_tx_o[0])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(FifoRptrCheck_A,
      u_tlul_adapter_sram.u_rspfifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_rptr,
      alert_tx_o[0])

endmodule : sram_ctrl
