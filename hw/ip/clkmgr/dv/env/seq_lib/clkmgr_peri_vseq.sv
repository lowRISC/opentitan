// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// peri test vseq
//
// This is more general than the corresponding smoke test since it randomizes the initial
// value of clk_enables CSR and the ip_clk_en input.
class clkmgr_peri_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_peri_vseq)

  `uvm_object_new

  rand logic [NUM_PERI-1:0] initial_enables;

  task body();
    update_csrs_with_reset_values();
    for (int i = 0; i < num_trans; ++i) begin
      logic [NUM_PERI-1:0] flipped_enables;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .ip_clk_en(ip_clk_en), .scanmode(scanmode));      

      csr_wr(.ptr(ral.clk_enables), .value(initial_enables));

      // Flip all bits of clk_enables.
      flipped_enables = initial_enables ^ ((1 << ral.clk_enables.get_n_bits()) - 1);
      csr_wr(.ptr(ral.clk_enables), .value(flipped_enables));
    end
  endtask : body
endclass : clkmgr_peri_vseq
