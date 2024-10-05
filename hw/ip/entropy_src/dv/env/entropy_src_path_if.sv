// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface deals with the force paths in ENTROPY_SRC interrupt and error tests

`define CORE \
    tb.dut.u_entropy_src_core
`define REPCNT \
    u_entropy_src_repcnt_ht.u_prim_max_tree_rep_cntr_max
`define BUCKET \
    u_entropy_src_bucket_ht.u_prim_max_tree_bin_cntr_max

interface entropy_src_path_if ();
  import uvm_pkg::*;

  string core_path = "tb.dut.u_entropy_src_core";

  function automatic string fifo_err_path(string fifo_name, string path_name);
    return {core_path, ".", fifo_name, "_", path_name};
  endfunction // fifo_err_path

  function automatic string sm_err_path(string which_sm);
    return {core_path, ".u_entropy_src_", which_sm, ".state_q"};
  endfunction // sm_err_path

  function automatic string cntr_err_path(string cntr_name, int which_cntr);
    case (cntr_name)
      "window": return {core_path, ".u_prim_count_window_cntr.cnt_q[1]"};
      "repcnt_ht": return {core_path, ".u_entropy_src_repcnt_ht",
                           $sformatf(".gen_cntrs[%0d]", which_cntr),
                           ".u_prim_count_rep_cntr.cnt_q[1]"};
      "repcnts_ht": return {core_path,
                            ".u_entropy_src_repcnts_ht.u_prim_count_rep_cntr.cnt_q[1]"};
      "adaptp_ht": return {core_path, ".u_entropy_src_adaptp_ht",
                           $sformatf(".gen_cntrs[%0d]", which_cntr),
                           ".u_prim_count_test_cnt.cnt_q[1]"};
      "bucket_ht": return {core_path, ".u_entropy_src_bucket_ht",
                           $sformatf(".gen_symbol_match[%0d]", which_cntr),
                           ".u_prim_count_bin_cntr.cnt_q[1]"};
      "markov_ht": return {core_path, ".u_entropy_src_markov_ht",
                           $sformatf(".gen_cntrs[%0d]", which_cntr),
                           ".u_prim_count_pair_cntr.cnt_q[1]"};
      default: begin
        `uvm_fatal("es_path_if", "Invalid cntr name!")
      end
    endcase // case (cntr_name)
  endfunction // cntr_err_path
   // Disable assertions that we expect to trigger when injecting errors
  task automatic assert_off_err();
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
    $assertoff(0, `CORE.AtReset_PosthtFifoPushedIntoDistrFifo_A);
    $assertoff(0, `CORE.Final_PosthtFifoPushedIntoDistrFifo_A);
    $assertoff(0, `CORE.AtReset_DistrFifoPushedIntoPreconFifo_A);
    $assertoff(0, `CORE.Final_DistrFifoPushedIntoPreconFifo_A);
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
  endtask
  function automatic void disable_entroy_drop_assertions();
    // Disable assertions which expect that no entropy is dropped between the esrng,
    // esbit and postht FIFOs.
    $assertoff(0, `CORE.AtReset_EsrngFifoPushedIntoEsbitOrPosthtFifos_A);
    $assertoff(0, `CORE.Final_EsrngFifoPushedIntoEsbitOrPosthtFifos_A);
    $assertoff(0, `CORE.AtReset_EsbitFifoPushedIntoPosthtFifo_A);
    $assertoff(0, `CORE.Final_EsbitFifoPushedIntoPosthtFifo_A);
    $assertoff(0, `CORE.AtReset_PosthtFifoPushedFromEsbitOrEsrngFifos_A);
    $assertoff(0, `CORE.Final_PosthtFifoPushedFromEsbitOrEsrngFifos_A);
    // TODO(#24085): Remove this assertoff once the issue is solved.
    $assertoff(0, `CORE.FifosEmptyWhenShaProcess_A);
  endfunction
endinterface // entropy_src_path_if

`undef CORE
`undef REPCNT
`undef BUCKET
