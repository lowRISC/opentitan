// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interface for LPG and crashdump output.
interface alert_handler_if(input clk, input rst_n);
  import uvm_pkg::*;
  import alert_pkg::*;
  import prim_mubi_pkg::*;
  import cip_base_pkg::*;
  import alert_handler_env_pkg::*;

  mubi4_t [NLpg-1:0] lpg_cg_en;
  mubi4_t [NLpg-1:0] lpg_rst_en;

  logic [NUM_ALERTS-1:0] alert_ping_reqs;
  logic [NUM_ESCS-1:0]   esc_ping_reqs;

  string msg_id = "alert_handler_if";

  function automatic void init();
    mubi4_t mubi_false_val = get_rand_mubi4_val(0, 1, 1);
    lpg_cg_en = '{default: mubi_false_val};
    lpg_rst_en = '{default: mubi_false_val};
  endfunction

  function automatic bit get_lpg_status(int index);
    check_lpg_index(index);
    return (lpg_cg_en[index] == MuBi4True || lpg_rst_en[index] == MuBi4True);
  endfunction

  function automatic void set_lpg_cg_en(int index);
    check_lpg_index(index);
    lpg_cg_en[index] = MuBi4True;
  endfunction

  function automatic void set_lpg_rst_en(int index);
    check_lpg_index(index);
    lpg_rst_en[index] = MuBi4True;
  endfunction

  function automatic void check_lpg_index(int index);
    if (index >= NLpg) begin
      `uvm_fatal(msg_id, $sformatf("Alert_handler has %0d LPGs but attempts to set index %0d",
                                   NLpg, index))
    end
  endfunction

  task automatic set_wait_cyc_mask(logic [PING_CNT_DW-1:0] val);
    static logic [PING_CNT_DW-1:0] val_static;
    begin
      val_static = val;
      force tb.dut.u_ping_timer.wait_cyc_mask_i = val_static;
    end
  endtask

  task automatic release_wait_cyc_mask();
    release tb.dut.u_ping_timer.wait_cyc_mask_i;
  endtask
endinterface
