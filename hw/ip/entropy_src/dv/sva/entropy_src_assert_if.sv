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

interface entropy_src_assert_if ();

  task automatic assert_off_alert ();

  endtask // assert_off_alert

  task automatic assert_on_alert ();

  endtask // assert_on_alert

  task automatic assert_off_err ();
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
    $assertoff(0, `CORE.AtReset_ValidRngBitsPushedIntoEsrngFifo_A);
    $assertoff(0, `CORE.Final_ValidRngBitsPushedIntoEsrngFifo_A);
    $assertoff(0, `CORE.AtReset_EsrngFifoPushedIntoEsbitOrPosthtFifos_A);
    $assertoff(0, `CORE.Final_EsrngFifoPushedIntoEsbitOrPosthtFifos_A);
    $assertoff(0, `CORE.AtReset_EsbitFifoPushedIntoPosthtFifo_A);
    $assertoff(0, `CORE.Final_EsbitFifoPushedIntoPosthtFifo_A);
    $assertoff(0, `CORE.AtReset_PosthtFifoPushedFromEsbitOrEsrngFifos_A);
    $assertoff(0, `CORE.Final_PosthtFifoPushedFromEsbitOrEsrngFifos_A);
    $assertoff(0, `CORE.AtReset_PosthtFifoPushedIntoPreconFifo_A);
    $assertoff(0, `CORE.Final_PosthtFifoPushedIntoPreconFifo_A);
    $assertoff(0, `CORE.AtReset_EsfinalFifoPushed_A);
    $assertoff(0, `CORE.Final_EsfinalFifoPushed_A);
    $assertoff(0, `CORE.AtReset_EsfinalFifoPushedPostStartup_A);
    $assertoff(0, `CORE.Final_EsfinalFifoPushedPostStartup_A);
    $assertoff(0, `CORE.AtReset_PreconFifoPushedPostStartup_A);
    $assertoff(0, `CORE.Final_PreconFifoPushedPostStartup_A);
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
