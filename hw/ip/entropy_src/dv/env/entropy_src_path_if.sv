// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface deals with the force paths in ENTROPY_SRC interrupt and error tests

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
endinterface // entropy_src_path_if
