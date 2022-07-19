// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// While running smoke test, assert illegal scanmode input
class rstmgr_sec_cm_scan_intersig_mubi_vseq extends rstmgr_smoke_vseq;

  `uvm_object_utils(rstmgr_sec_cm_scan_intersig_mubi_vseq)

  `uvm_object_new

  task body();
    disable_assert();
    fork
      begin
        fork
          super.body();
          add_noise();
        join_any
        disable fork;
      end
    join
  endtask : body

  function void disable_assert();
    $assertoff(0, "prim_mubi4_sync");
  endfunction : disable_assert

  task add_noise();
    int delay;

    forever begin
      cfg.clk_rst_vif.wait_clks(1);
      // If scan_rst_ni is active we assume super is doing a scan reset, so keep scanmode_i True.
      if (cfg.rstmgr_vif.scan_rst_ni == 1'b1) begin
        cfg.rstmgr_vif.scanmode_i = get_rand_mubi4_val(0, 0, 1);
      end else begin
        cfg.rstmgr_vif.scanmode_i = prim_mubi_pkg::MuBi4True;
      end
      cfg.io_div4_clk_rst_vif.wait_clks(scanmode_to_scan_rst_cycles);
      delay = $urandom_range(0, 30);
      cfg.clk_rst_vif.wait_clks(delay);
    end
  endtask : add_noise
endclass : rstmgr_sec_cm_scan_intersig_mubi_vseq
