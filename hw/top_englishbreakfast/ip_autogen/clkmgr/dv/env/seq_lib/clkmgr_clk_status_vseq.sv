// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This tests the transitions of the various clock status outputs for random settings of the
// various ip_clk_en inputs.
//
// The checks are done via SVA in clkmgr_pwrmgr_sva_if.
class clkmgr_clk_status_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_clk_status_vseq)

  `uvm_object_new

  function void post_randomize();
    super.post_randomize();
    // Disable scanmode since it is not interesting.
    scanmode = prim_mubi_pkg::MuBi4False;
  endfunction

  task body();
    for (int i = 0; i < num_trans; ++i) begin
      cfg.clk_rst_vif.wait_clks(4);
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode));
      control_ip_clocks();

      // If some units were not idle, make them so.
      idle = '1;
      // Wait for idle to percolate.
      cfg.clk_rst_vif.wait_clks(10);
    end
    // And set it back to more common values for stress tests.
    initialize_on_start();
  endtask : body
endclass : clkmgr_clk_status_vseq
