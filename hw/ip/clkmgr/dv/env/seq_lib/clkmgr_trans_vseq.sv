// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// trans test vseq
// This is a more randomized version of the corresponding test in the smoke sequence.
// Starts with random units busy, set the hints at random. The idle units whose hint bit is off
// will be disabled, but the others will remain enabled. Then all units are made idle to check 
// that status matches hints. Prior to the next round this raises all hints to avoid units whose
// clock is off but are not idle.
//
// Notice one of the otbn transactional units is on the io_div4 clock, so there are some extra
// cycles of synchronization.

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
      cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode));
      control_ip_clocks();
      cfg.clk_rst_vif.wait_clks(10);
      `uvm_info(`gfn, $sformatf("Updating hints to 0x%0x", initial_hints), UVM_MEDIUM)
      csr_wr(.ptr(ral.clk_hints), .value(initial_hints));

      // Extra wait because of clk_io_div4 synchronizers.
      cfg.io_clk_rst_vif.wait_clks(IO_DIV4_SYNC_CYCLES);
      // We expect the status to be determined by hints and idle.
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      bool_idle = mubi_hintables_to_hintables(idle);
      `DV_CHECK_EQ(value, initial_hints | ~bool_idle, $sformatf(
                   "Busy units have status high: hints=0x%x, idle=0x%x", initial_hints, bool_idle))

      // Setting all idle should make hint_status match hints.
      cfg.clkmgr_vif.update_idle({NUM_TRANS{MuBi4True}});
      cfg.io_clk_rst_vif.wait_clks(IO_DIV4_SYNC_CYCLES);
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      `DV_CHECK_EQ(value, initial_hints, "All idle: units status matches hints")

      // Now set all hints, and the status should also be all ones.
      csr_wr(.ptr(ral.clk_hints), .value('1));
      cfg.io_clk_rst_vif.wait_clks(IO_DIV4_SYNC_CYCLES);
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      // We expect all units to be on.
      `DV_CHECK_EQ(value, '1, "All idle and all hints high: units status should be high")
      // Set hints to the reset value for stress tests.
      csr_wr(.ptr(ral.clk_hints), .value(ral.clk_hints.get_reset()));
    end
  endtask : body

endclass : clkmgr_trans_vseq
