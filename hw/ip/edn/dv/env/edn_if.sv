// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is an EDN interface.
// It deals with the force paths in EDN interrupt and error tests,
// and helps pass the disable signal to the csrng agent.

interface edn_if(input clk, input rst_n);

  import uvm_pkg::*;

  string core_path = "tb.dut.u_edn_core";
  logic edn_disable_o;

  function automatic string fifo_err_path(string fifo_name, string which_path);
    return {core_path, ".", fifo_name, "_", which_path};
  endfunction // fifo_err_path

  function automatic string sm_err_path(string which_sm, int ep_idx = 0);
    case (which_sm)
      "edn_ack_sm": begin
        string ep_blk_path = $sformatf(".gen_ep_blk[%0d]", ep_idx);
        return {core_path, ep_blk_path, ".u_edn_ack_sm_ep.state_q"};
      end
      "edn_main_sm": return {core_path, ".u_edn_main_sm.state_q"};
      default: `uvm_fatal("edn_if", "Invalid sm name!")
    endcase // case (which_sm)
  endfunction // sm_err_path

  function automatic string cntr_err_path();
    return {core_path, ".u_prim_count_max_reqs_cntr.err_o"};
  endfunction // cntr_err_path

  function automatic drive_edn_disable(bit val);
    edn_disable_o = val;
  endfunction

endinterface // edn_if
