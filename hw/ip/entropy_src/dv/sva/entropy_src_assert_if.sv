// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface: entropy_src_assert_if
// Description: Asserts interface to turn off assertions that have long paths

`define PATH1 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_fips_en
`define PATH2 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_data_reg_en
`define PATH3 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_module_en
`define PATH4 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_rng_bit_en
`define PATH5 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_fw_ov_mode
`define PATH6 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_fw_ov_entropy_insert
`define PATH7 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_route
`define PATH8 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_type
`define PATH9 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_enable
`define PATH10 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_enable_pulse
`define CORE \
    tb.dut.u_entropy_src_core
`define SHA3 \
    u_sha3.u_keccak.u_round_count
`define REPCNT \
    u_entropy_src_repcnt_ht.u_prim_max_tree_rep_cntr_max
`define BUCKET \
    u_entropy_src_bucket_ht.u_prim_max_tree_bin_cntr_max

interface entropy_src_assert_if
  import entropy_src_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  input entropy_src_hw_if_req_t entropy_src_hw_if_i
);

  logic cs_aes_halt_active_d, cs_aes_halt_active_q;
  logic keccak_active_d, keccak_active_q;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      cs_aes_halt_active_q <= 1'b0;
      keccak_active_q <= 1'b0;
    end else begin
      cs_aes_halt_active_q <= cs_aes_halt_active_d;
      keccak_active_q <= keccak_active_d;
    end
  end
  `ASSERT_KNOWN(CsAesHaltActiveKnown_A, cs_aes_halt_active_q)
  `ASSERT_KNOWN(KeccakActiveKnown_A, keccak_active_q)

  assign keccak_active_d = `CORE.u_sha3.u_keccak.run_i ? 1'b1 :      // set when Keccak starts
                           `CORE.u_sha3.u_keccak.complete_o ? 1'b0 : // clear when Keccak completes
                           keccak_active_q;                          // keep otherwise

  always_comb begin
    cs_aes_halt_active_d = cs_aes_halt_active_q;
    if (!cs_aes_halt_active_q) begin
      // CS AES Halt becomes active on req/ack handshake.
      if (`CORE.cs_aes_halt_o.cs_aes_halt_req && `CORE.cs_aes_halt_i.cs_aes_halt_ack) begin
        cs_aes_halt_active_d = 1'b1;
      end
    end else begin
      if (!`CORE.cs_aes_halt_o.cs_aes_halt_req) begin
        // CS AES halt becomes inactive when req drops.
        cs_aes_halt_active_d = 1'b0;
      end
    end
  end

  // TODO: Remove this (debug only).
  //
  // Print a warning when keccak is active but cs_aes_halt isn't, outside the already known
  // scenarios.
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (rst_ni && keccak_active_q && !cs_aes_halt_active_q) begin
      entropy_src_main_sm_pkg::state_e state;
      string msg;
      state = `CORE.u_entropy_src_main_sm.state_q;
      if (!(state inside {entropy_src_main_sm_pkg::FWInsertMsg,
                          entropy_src_main_sm_pkg::Sha3Prep,
                          entropy_src_main_sm_pkg::StartupPhase1,
                          entropy_src_main_sm_pkg::StartupPass1,
                          entropy_src_main_sm_pkg::StartupFail1,
                          entropy_src_main_sm_pkg::ContHTRunning,
                          entropy_src_main_sm_pkg::Idle,
                          entropy_src_main_sm_pkg::AlertHang})) begin
        msg = $sformatf("keccak active without CSRNG AES halted in state %0s", state.name());
        `dv_warning(msg)
      end
    end
  end

  // Keccak may only be active if CSRNG's AES is halted.
  `ASSERT(KeccakActiveOnlyWhenCsAesHaltActive_A, keccak_active_q |-> cs_aes_halt_active_q)

  // When CSRNG's AES gets halted, Keccak must be activated in the next dozens of cycles or
  // entropy_src must be disabled.  This assertion prevents spurious halts of CSRNG's AES.
  //
  // TODO: Doesn't work yet (has to take disabling into consideration, at least), but is of
  // secondary concern.
  // `ASSERT(CsAesHaltActiveOnlyAWhenKeccakActive_A,
  //         cs_aes_halt_active_q |-> ##[0:36] keccak_active_q)

  task automatic assert_off_alert ();

  endtask // assert_off_alert

  task automatic assert_on_alert ();

  endtask // assert_on_alert

  task automatic assert_off_err ();
    $assertoff(0, CsAesHaltActiveKnown_A);
    $assertoff(0, KeccakActiveKnown_A);
    $assertoff(0, KeccakActiveOnlyWhenCsAesHaltActive_A);
    // $assertoff(0, CsAesHaltActiveOnlyAWhenKeccakActive_A); // TODO: see above
    $assertoff(0, tb.dut.AlertTxKnownO_A);
    $assertoff(0, tb.dut.IntrEsFifoErrKnownO_A);
    $assertoff(0, tb.dut.EsHwIfEsAckKnownO_A);
    $assertoff(0, tb.dut.EsHwIfEsBitsKnownO_A);
    $assertoff(0, tb.dut.EsHwIfEsFipsKnownO_A);
    $assertoff(0, tb.dut.EsXhtEntropyBitKnownO_A);
    $assertoff(0, tb.dut.IntrEsEntropyValidKnownO_A);
    $assertoff(0, tb.dut.IntrEsHealthTestFailedKnownO_A);
    $assertoff(0, tb.dut.tlul_assert_device.dKnown_A);
    $assertoff(0, tb.dut.tlul_assert_device.gen_device.dDataKnown_A);
    $assertoff(0, tb.dut.gen_alert_tx[0].u_prim_alert_sender.AlertPKnownO_A);
    $assertoff(0, tb.dut.gen_alert_tx[0].u_prim_alert_sender.gen_async_assert.DiffEncoding_A);
    $assertoff(0, `CORE.u_sha3.FsmKnown_A);
    $assertoff(0, `CORE.u_sha3.MuxSelKnown_A);
    $assertoff(0, `CORE.u_entropy_src_main_sm.u_state_regs_A);
    $assertoff(0, `CORE.u_entropy_src_ack_sm.u_state_regs_A);
    $assertoff(0, `CORE.u_prim_fifo_sync_esfinal.DepthKnown_A);
    $assertoff(0, `CORE.u_prim_fifo_sync_esfinal.RvalidKnown_A);
    $assertoff(0, `CORE.u_prim_fifo_sync_esfinal.WreadyKnown_A);
    $assertoff(0, `CORE.u_prim_fifo_sync_esrng.DataKnown_A);
    $assertoff(0, `CORE.u_entropy_src_adaptp_ht.u_sum.SumComputation_A);
    $assertoff(0, `CORE.u_entropy_src_markov_ht.u_sum.SumComputation_A);
    $assertoff(0, `CORE.u_entropy_src_adaptp_ht.u_min.ValidInImpliesValidOut_A);
    $assertoff(0, `CORE.u_entropy_src_adaptp_ht.u_max.ValidInImpliesValidOut_A);
    $assertoff(0, `CORE.u_entropy_src_markov_ht.u_min.ValidInImpliesValidOut_A);
    $assertoff(0, `CORE.u_entropy_src_markov_ht.u_max.ValidInImpliesValidOut_A);
    $assertoff(0, `CORE.u_sha3.u_keccak.gen_unmask_st_chk.UnmaskValidStates_A);
    $assertoff(0, `CORE.`REPCNT.ValidInImpliesValidOut_A);
    $assertoff(0, `CORE.`BUCKET.ValidInImpliesValidOut_A);
  endtask // assert_off_err
endinterface
