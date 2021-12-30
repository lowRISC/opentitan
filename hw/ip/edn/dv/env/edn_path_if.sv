// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface deals with the force paths in EDN interrupt and error tests

interface edn_path_if
(
  input edn_i
);

  import uvm_pkg::*;

  string core_path = "tb.dut.u_edn_core";

  function automatic string fifo_err_path(string fifo_name, string which_path);
    return {core_path, ".", fifo_name, "_", which_path};
  endfunction // fifo_err_path

  function automatic string sm_err_path(string which_sm);
    case (which_sm)
      "edn_ack_sm": return {core_path, ".gen_ep_blk[0].u_edn_ack_sm_ep.state_q"};
      "edn_main_sm": return {core_path, ".u_edn_main_sm.state_q"};
      default: `uvm_fatal("edn_path_if", "Invalid sm name!")
    endcase // case (which_sm)
  endfunction // sm_err_path

  function automatic string cntr_err_path();
    return {core_path, ".u_prim_count_max_reqs_cntr.gen_cross_cnt_hardening.msb"};
  endfunction // cntr_err_path
endinterface // edn_path_if
