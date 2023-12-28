// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_sba_debug_disabled_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_sba_debug_disabled_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task sba_access();
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1));
    req = sba_access_item::type_id::create("req");
    randomize_req(req);
    cfg.debugger.sba_access(req);
  endtask

  task body();
    repeat ($urandom_range(1, 10)) begin
      sba_access();
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      cfg.rv_dm_vif.lc_hw_debug_en = get_rand_lc_tx_val(.t_weight(0), .f_weight(1), .other_weight(4));
      sba_access();
      `DV_CHECK_EQ(req.is_err, SbaErrNone)
    end
  endtask : body
endclass  : rv_dm_sba_debug_disabled_vseq
