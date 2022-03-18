// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_esc_clk_rst_malfunc_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_esc_clk_rst_malfunc_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task body();
    `uvm_info(`gfn, $sformatf("JDONDBG:I am body"), UVM_MEDIUM)
    // before body, fast state become active state
    #1us;
    repeat(10)begin
      add_noise();
      clear_noise();
    end

  endtask : body

  task add_noise();
    int delay = $urandom_range(10,50);
    randcase
      1:void'(uvm_hdl_force("tb.dut.rst_esc_ni", 0));
      1:void'(uvm_hdl_force("tb.dut.clk_esc_i", 0));
    endcase // randcase
    #(delay * 1us);
  endtask // add_noise

  task clear_noise();
    int delay = $urandom_range(1,5);
    void'(uvm_hdl_release("tb.dut.rst_esc_ni"));
    void'(uvm_hdl_release("tb.dut.clk_esc_i"));
    #(delay * 100ns);
  endtask // clear_noise
endclass
