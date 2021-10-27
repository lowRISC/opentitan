// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The wakeup test randomly enables wakeups, info capture, and interrupts,
// and sends wakeups at random times.
class pwrmgr_wakeup_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_wakeup_vseq)

  `uvm_object_new

  rand bit                                disable_wakeup_capture;
  constraint wakeups_c {wakeups != 0;}

  rand bit [pwrmgr_reg_pkg::NumWkups-1:0] wakeup_en;
  constraint wakeup_en_c {
    solve wakeups before wakeup_en;
    |(wakeup_en & wakeups) == 1'b1;
  }
  rand bit core_clk_en;
  rand bit io_clk_en;
  rand bit usb_clk_en_lp;
  rand bit usb_clk_en_active;
  rand bit main_pd_n;

  task body();
    logic [TL_DW-1:0] value;
    bit [pwrmgr_reg_pkg::NumWkups-1:0] enabled_wakeups;

    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(0));
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Enable wakeups.
      enabled_wakeups = wakeup_en & wakeups;
      `DV_CHECK(enabled_wakeups, $sformatf(
                "Some wakeup must be enabled: wkups=%b, wkup_en=%b",
                wakeups,
                wakeup_en
                ))
      `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", enabled_wakeups), UVM_MEDIUM)
      csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeup_en));
      csr_wr(.ptr(ral.wake_info_capture_dis), .value(disable_wakeup_capture));
      wait_for_csr_to_propagate_to_slow_domain();

      // Initiate low power transition.
      ral.control.core_clk_en.set(core_clk_en);
      ral.control.io_clk_en.set(io_clk_en);
      ral.control.usb_clk_en_lp.set(usb_clk_en_lp);
      ral.control.main_pd_n.set(main_pd_n);
      ral.control.low_power_hint.set(1'b1);
      // Disable assertions when main power is down.
      control_assertions(main_pd_n);

      csr_update(.csr(ral.control));
      cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
      fast_to_low_power();
      if (ral.control.main_pd_n.get_mirrored_value() == 1'b0) begin
        wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
      end

      // Now bring it back.
      cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
      cfg.pwrmgr_vif.update_wakeups(wakeups);
      // Check wake_status prior to wakeup, or the unit requesting wakeup will have been reset.
      cfg.slow_clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(enabled_wakeups),
                   .err_msg("failed wake_status check"));
      `uvm_info(`gfn, $sformatf("Got wake_status=0x%x", enabled_wakeups), UVM_MEDIUM)
      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);
      cfg.pwrmgr_vif.update_wakeups('0);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from wakeup", UVM_MEDIUM)

      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0),
                   .err_msg("failed reset_status check"));
      if (disable_wakeup_capture) begin
        csr_rd_check(.ptr(ral.wake_info.reasons),
                     .compare_value('0));
      end else begin
        csr_rd_check(.ptr(ral.wake_info.reasons),
                     .compare_value(enabled_wakeups));
      end
      csr_rd_check(.ptr(ral.wake_info.fall_through), .compare_value(1'b0));
      csr_rd_check(.ptr(ral.wake_info.abort), .compare_value(1'b0));
      // Clear wake_info.
      csr_wr(.ptr(ral.wake_info), .value('1));

      // Wait for interrupt to be generated whether or not it is enabled.
      cfg.slow_clk_rst_vif.wait_clks(10);
    end
  endtask

endclass : pwrmgr_wakeup_vseq
