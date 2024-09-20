// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// While running smoke test, assert illegal scanmode input
class rstmgr_sec_cm_scan_intersig_mubi_vseq extends rstmgr_smoke_vseq;

  `uvm_object_utils(rstmgr_sec_cm_scan_intersig_mubi_vseq)

  `uvm_object_new

  task body();
    fork
      begin : isolation_fork
        fork
          super.body();
          add_noise();
        join_any
        disable fork;
      end
    join
  endtask : body

  task add_noise();
    int delay;

    forever begin
      // If scan_rst_ni is active we assume super is doing a scan reset, so keep scanmode_i True.
      if (cfg.rstmgr_vif.scan_rst_ni == 1'b1) begin
        cfg.rstmgr_vif.scanmode_i = get_rand_mubi4_val(0, 1, 4);
      end else begin
        cfg.rstmgr_vif.scanmode_i = prim_mubi_pkg::MuBi4True;
      end
      delay = $urandom_range(5, 30);
      fork
        // This waits for a certain number of cycles or for a change in scan_rst_ni,
        //  whichever is sooner, or it could end up skipping a full scan reset.
        begin : isolation_fork
          fork
            @(edge cfg.rstmgr_vif.scan_rst_ni);
            cfg.clk_rst_vif.wait_clks(delay);
          join_any
          disable fork;
        end
      join
      // Somehow without this VCS will scan_rst_ni transitions to 0.
      #0;
    end
  endtask : add_noise
endclass : rstmgr_sec_cm_scan_intersig_mubi_vseq
