// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class clkmgr_smoke_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_smoke_vseq)

  `uvm_object_new

  constraint io_ip_clk_en_on_c {io_ip_clk_en == 1'b1;}
  constraint main_ip_clk_en_on_c {main_ip_clk_en == 1'b1;}
  constraint usb_ip_clk_en_on_c {usb_ip_clk_en == 1'b1;}
  constraint all_busy_c {idle == IdleAllBusy;}

  task body();
    cfg.clk_rst_vif.wait_clks(10);
    test_jitter();
    test_peri_clocks();
    test_trans_clocks();
  endtask : body

  // Simply flip the jitter enable CSR. The side-effects are checked in the scoreboard.
  // This needs to be done outside the various CSR tests, since they update the jitter_enable
  // CSR, but the scoreboard is disabled for those tests.
  task test_jitter();
    prim_mubi_pkg::mubi4_t jitter_value;
    for (int i = 0; i < (1 << $bits(prim_mubi_pkg::mubi4_t)); ++i) begin
      jitter_value = prim_mubi_pkg::mubi4_t'(i);
      csr_wr(.ptr(ral.jitter_enable), .value(jitter_value));
      csr_rd_check(.ptr(ral.jitter_enable), .compare_value(jitter_value));
      // And set it back.
      cfg.clk_rst_vif.wait_clks(6);
      csr_wr(.ptr(ral.jitter_enable), .value('0));
      csr_rd_check(.ptr(ral.jitter_enable), .compare_value('0));
    end
  endtask

  // Flips all clk_enables bits from the reset value with all enabled. All is checked
  // via assertions in clkmgr_if.sv and behavioral code in the scoreboard.
  task test_peri_clocks();
    // Flip all bits of clk_enables.
    peri_enables_t value = ral.clk_enables.get();
    peri_enables_t flipped_value;
    csr_rd(.ptr(ral.clk_enables), .value(value));
    flipped_value = value ^ ((1 << ral.clk_enables.get_n_bits()) - 1);
    csr_wr(.ptr(ral.clk_enables), .value(flipped_value));

    // And set it back to the reset value for stress tests.
    cfg.clk_rst_vif.wait_clks(1);
    csr_wr(.ptr(ral.clk_enables), .value(ral.clk_enables.get_reset()));
  endtask : test_peri_clocks

  // Starts with all units busy, and for each one this clears the hint and reads the hint status,
  // expecting it to remain at 1 since the unit is busy; then it sets the corresponding idle bit
  // and reads status again, expecting it to be low.
  //
  // We disable the value checks when reset is active since the reads return unpredictable data.
  task test_trans_clocks();
    trans_e trans;
    logic bit_value;
    logic [TL_DW-1:0] value;
    mubi_hintables_t idle;
    hintables_t bool_idle;
    typedef struct {
      trans_e unit;
      uvm_reg_field hint_bit;
      uvm_reg_field value_bit;
    } trans_descriptor_t;
    trans_descriptor_t trans_descriptors[NUM_TRANS] = '{
        '{TransAes, ral.clk_hints.clk_main_aes_hint, ral.clk_hints_status.clk_main_aes_val},
        '{TransHmac, ral.clk_hints.clk_main_hmac_hint, ral.clk_hints_status.clk_main_hmac_val},
        '{TransKmac, ral.clk_hints.clk_main_kmac_hint, ral.clk_hints_status.clk_main_kmac_val},
        '{TransOtbn, ral.clk_hints.clk_main_otbn_hint, ral.clk_hints_status.clk_main_otbn_val}
    };
    idle = 0;
    // Changes in idle take at least 10 cycles to stick.
    cfg.clkmgr_vif.update_idle(idle);
    cfg.clk_rst_vif.wait_clks(IDLE_SYNC_CYCLES);

    trans = trans.first;
    csr_rd(.ptr(ral.clk_hints), .value(value));
    `uvm_info(`gfn, $sformatf("Starting hints at 0x%0x, idle at 0x%x", value, idle), UVM_MEDIUM)
    do begin
      trans_descriptor_t descriptor = trans_descriptors[int'(trans)];
      `uvm_info(`gfn, $sformatf("Clearing %s hint bit", descriptor.unit.name), UVM_MEDIUM)
      csr_wr(.ptr(descriptor.hint_bit), .value(1'b0));
      csr_rd(.ptr(descriptor.value_bit), .value(bit_value));
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(bit_value, 1'b1, $sformatf(
                     "%s hint value cannot drop while busy", descriptor.unit.name()))
      end
      `uvm_info(`gfn, $sformatf("Setting %s idle bit", descriptor.unit.name), UVM_MEDIUM)
      cfg.clk_rst_vif.wait_clks(1);
      idle[trans] = prim_mubi_pkg::MuBi4True;
      cfg.clkmgr_vif.update_idle(idle);
      // Some cycles for the logic to settle.
      cfg.clk_rst_vif.wait_clks(IDLE_SYNC_CYCLES);
      csr_rd(.ptr(descriptor.value_bit), .value(bit_value));
      if (!cfg.under_reset) begin
        `DV_CHECK_EQ(bit_value, 1'b0, $sformatf(
                     "%s hint value should drop when idle", descriptor.unit.name()))
      end
      trans = trans.next();
    end while (trans != trans.first);
    csr_wr(.ptr(ral.clk_hints), .value(ral.clk_hints.get_reset()));
  endtask : test_trans_clocks
endclass : clkmgr_smoke_vseq
