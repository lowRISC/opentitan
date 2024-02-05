// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the control of the peripheral clocks using clk_enables CSR.
//
// This is more general than the corresponding smoke test since it randomizes the initial
// value of clk_enables CSR and the ip_clk_en input.
class clkmgr_peri_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_peri_vseq)

  `uvm_object_new

  rand peri_enables_t initial_enables;

  // The clk_enables CSR cannot be manipulated in low power mode.
  constraint io_ip_clk_en_on_c {io_ip_clk_en == 1'b1;}
  constraint main_ip_clk_en_on_c {main_ip_clk_en == 1'b1;}
  // ICEBOX(#17963) randomize the usb clk enable.
  constraint usb_ip_clk_en_on_c {usb_ip_clk_en == 1'b1;}

  task body();
    for (int i = 0; i < num_trans; ++i) begin
      peri_enables_t flipped_enables;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode));
      control_ip_clocks();
      csr_wr(.ptr(ral.clk_enables), .value(initial_enables));

      // Flip all bits of clk_enables.
      flipped_enables = initial_enables ^ ((1 << ral.clk_enables.get_n_bits()) - 1);
      csr_wr(.ptr(ral.clk_enables), .value(flipped_enables));
      // Allow some time for the side-effects to be observed: the dv environment sets the CSRs
      // clock frequency randomly, so it may run too fast and the the updates may become a glitch
      // that ends up not sampled in the SVAs.
      cfg.clk_rst_vif.wait_clks(4);
    end
    // And set it back to the reset value for stress tests.
    cfg.clk_rst_vif.wait_clks(1);
    csr_wr(.ptr(ral.clk_enables), .value(ral.clk_enables.get_reset()));
  endtask : body
endclass : clkmgr_peri_vseq
