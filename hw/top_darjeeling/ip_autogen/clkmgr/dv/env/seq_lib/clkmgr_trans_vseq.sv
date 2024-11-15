// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// trans test vseq
// This is a more randomized version of the corresponding test in the smoke sequence.
// Starts with random units busy, set the hints at random. The idle units whose hint bit is off
// will be disabled, but the others will remain enabled. Then all units are made idle to check
// that status matches hints. Prior to the next round this raises all hints so all unit clocks are
// running.
//
// Transitions to turn off the clock only go through if idle is asserted for at least 10 main
// cycles, and there is additional synchronizer overhead.
//
// The checks for whether each unit's clock are running are done in SVA. This sequence only
// explicitly checks hints_status.

class clkmgr_trans_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_trans_vseq)

  `uvm_object_new

  rand hintables_t initial_hints;

  // The clk_hints CSR cannot be manipulated in low power mode.
  constraint io_ip_clk_en_on_c {io_ip_clk_en == 1'b1;}
  constraint main_ip_clk_en_on_c {main_ip_clk_en == 1'b1;}
  constraint usb_ip_clk_en_on_c {usb_ip_clk_en == 1'b1;}

  task body();
    for (int i = 0; i < num_trans; ++i) begin
      logic bit_value;
      hintables_t value;
      hintables_t bool_idle;

      `DV_CHECK_RANDOMIZE_FATAL(this)

      csr_rd(.ptr(ral.clk_hints_status), .value(value));

      `uvm_info(`gfn, $sformatf("Initial clk_hints_status: %b", value), UVM_MEDIUM)
      cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode));

      // add random value if mubi idle test
      if (mubi_mode == ClkmgrMubiIdle) drive_idle(idle);
      print_mubi_hintable(idle);
      control_ip_clocks();
      `uvm_info(`gfn, $sformatf("Idle = 0x%x", cfg.clkmgr_vif.idle_i), UVM_MEDIUM)
      cfg.clk_rst_vif.wait_clks(10);
      `uvm_info(`gfn, $sformatf("Updating hints to 0x%0x", initial_hints), UVM_MEDIUM)
      csr_wr(.ptr(ral.clk_hints), .value(initial_hints));

      // Extra wait because of synchronizers plus counters.
      cfg.clk_rst_vif.wait_clks(IDLE_SYNC_CYCLES);
      // We expect the status to be determined by hints and idle, ignoring scanmode.
      bool_idle = mubi_hintables_to_hintables(idle);
      value = initial_hints | ~bool_idle;
      csr_rd_check(.ptr(ral.clk_hints_status), .compare_value(value),
                   .err_msg($sformatf(
                       "Busy units have status high: hints=0x%x, idle=0x%x",
                       initial_hints,
                       bool_idle
                   )));

      // Setting all idle should make hint_status match hints.
      `uvm_info(`gfn, "Setting all units idle", UVM_MEDIUM)
      cfg.clkmgr_vif.update_idle({NUM_TRANS{MuBi4True}});
      cfg.clk_rst_vif.wait_clks(IDLE_SYNC_CYCLES);

      csr_rd_check(.ptr(ral.clk_hints_status), .compare_value(initial_hints),
                   .err_msg("All idle: expect status matches hints"));

      // Now set all hints, and the status should also be all ones.
      value = '1;
      csr_wr(.ptr(ral.clk_hints), .value(value));
      cfg.clk_rst_vif.wait_clks(IDLE_SYNC_CYCLES);
      // We expect all units to be on.
      csr_rd_check(.ptr(ral.clk_hints_status), .compare_value(value),
                   .err_msg("All idle and all hints high: units status should be high"));

      // Set hints to the reset value for stress tests.
      csr_wr(.ptr(ral.clk_hints), .value(ral.clk_hints.get_reset()));
    end
  endtask : body

  task drive_idle(ref mubi_hintables_t tbl);
    int period;
    mubi_hintables_t rand_idle;
    foreach (rand_idle[i])
      rand_idle[i] = get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1));

    @cfg.clkmgr_vif.trans_cb;
    cfg.clkmgr_vif.idle_i = rand_idle;

    tbl = rand_idle;
  endtask : drive_idle
endclass : clkmgr_trans_vseq
