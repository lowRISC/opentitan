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

  mubi4_t [NLpg-1:0] lpg_cg_en;
  mubi4_t [NLpg-1:0] lpg_rst_en;

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
endinterface
