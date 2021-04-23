// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class clkmgr_smoke_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_smoke_vseq)

  `uvm_object_new

  constraint enable_ip_clk_en { ip_clk_en == 1'b1; }
  constraint all_busy { idle == '0; }

  task body();
    cfg.clk_rst_vif.wait_clks(10);
    test_peri_clocks();
    test_trans_clocks();
  endtask : body

  // Flips all clk_enables bits from the reset value with all enabled. All is
  // checked via assertions in clkmgr_if.sv.
  task test_peri_clocks();
    // Flip all bits of clk_enables.
    logic [NUM_PERI-1:0] value = ral.clk_enables.get();
    logic [NUM_PERI-1:0] flipped_value;
    csr_rd(.ptr(ral.clk_enables), .value(value));
    flipped_value = value ^ ((1 << ral.clk_enables.get_n_bits()) - 1);
    csr_wr(.ptr(ral.clk_enables), .value(flipped_value));
  endtask : test_peri_clocks

  // Starts with all units busy, and for each one this clears the hint and reads the
  // hint status, expecting it to remain at 1 since the unit is busy; then it sets
  // the corresponding idle bit and reads status again, expecting it to be low.
  task test_trans_clocks();
    trans_e trans;
    logic bit_value;
    logic [TL_DW-1:0] value;
    typedef struct {
      trans_e       unit;
      uvm_reg_field hint_bit;
      uvm_reg_field value_bit;
    } trans_descriptor_t;
    trans_descriptor_t trans_descriptors[NUM_TRANS] = '{
        '{TransAes, ral.clk_hints.clk_main_aes_hint, ral.clk_hints_status.clk_main_aes_val},
        '{TransHmac, ral.clk_hints.clk_main_hmac_hint, ral.clk_hints_status.clk_main_hmac_val},
        '{TransKmac, ral.clk_hints.clk_main_kmac_hint, ral.clk_hints_status.clk_main_kmac_val},
        '{TransAes, ral.clk_hints.clk_main_otbn_hint, ral.clk_hints_status.clk_main_otbn_val}
    };

    cfg.clkmgr_vif.update_idle(0);
    trans = trans.first;
    csr_rd(.ptr(ral.clk_hints), .value(value));
    `uvm_info(`gfn, $sformatf("Updating hints to 0x%0x", value), UVM_MEDIUM)
    cfg.clkmgr_vif.update_hints(value);
    do begin
      trans_descriptor_t descriptor = trans_descriptors[int'(trans)];
      `uvm_info(`gfn, $sformatf("Clearing %s hint bit", descriptor.unit.name), UVM_MEDIUM)
      csr_wr(.ptr(descriptor.hint_bit), .value(1'b0));
      csr_rd(.ptr(descriptor.value_bit), .value(bit_value));
      `DV_CHECK_EQ(bit_value, 1'b1,
                   $sformatf("%s hint value cannot drop while busy", descriptor.unit.name()))

      `uvm_info(`gfn, $sformatf("Setting %s idle bit", descriptor.unit.name), UVM_MEDIUM)
      cfg.clkmgr_vif.wait_clks(1);
      cfg.clkmgr_vif.update_trans_idle(1'b1, trans);
      // Some cycles for the logic to settle.
      cfg.clk_rst_vif.wait_clks(3);
      csr_rd(.ptr(descriptor.value_bit), .value(bit_value));
      `DV_CHECK_EQ(bit_value, 1'b0,
                   $sformatf("%s hint value should drop when idle",  descriptor.unit.name()))
      trans = trans.next();
    end while (trans != trans.first);
  endtask : test_trans_clocks

endclass : clkmgr_smoke_vseq
