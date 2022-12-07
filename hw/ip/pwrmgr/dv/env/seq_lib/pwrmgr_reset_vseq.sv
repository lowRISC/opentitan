// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The reset test randomly introduces external resets, ndm resets, power glitches, and escalation
// resets.
class pwrmgr_reset_vseq extends pwrmgr_base_vseq;

  `uvm_object_utils(pwrmgr_reset_vseq)
  `uvm_object_new

  constraint wakeups_c {wakeups == 0;}
  constraint wakeups_en_c {wakeups_en == 0;}

  function void post_randomize();
    sw_rst_from_rstmgr = get_rand_mubi4_val(.t_weight(8), .f_weight(4), .other_weight(4));
    super.post_randomize();
  endfunction

  task body();
    logic [TL_DW-1:0] value;
    resets_t enabled_resets;
    wait_for_fast_fsm_active();

    check_reset_status('0);
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));
      enabled_resets = resets_en & resets;
      `uvm_info(`gfn, $sformatf(
                "Enabled resets=0x%x, power_reset=%b, escalation=%b, sw_reset=%b, ndm_reset=%b",
                enabled_resets,
                power_glitch_reset,
                escalation_reset,
                sw_rst_from_rstmgr == prim_mubi_pkg::MuBi4True,
                ndm_reset
                ), UVM_MEDIUM)

      csr_wr(.ptr(ral.reset_en[0]), .value(resets_en));
      // This is necessary to propagate reset_en.
      wait_for_csr_to_propagate_to_slow_domain();

      // Trigger resets. The glitch is sent prior to the externals since if it is delayed
      // it will cause a separate reset after the externals, which complicates the checks.
      if (power_glitch_reset) send_power_glitch();
      cfg.clk_rst_vif.wait_clks(cycles_before_reset);

      `uvm_info(`gfn, $sformatf("Sending resets=0x%x", resets), UVM_MEDIUM)
      cfg.pwrmgr_vif.update_resets(resets);
      `uvm_info(`gfn, $sformatf("Sending sw reset from rstmgr=%b", sw_rst_from_rstmgr), UVM_MEDIUM)
      if (escalation_reset) begin
        send_escalation_reset();
        // Wait for the alert to propagate to fault_status?
      end
      cfg.pwrmgr_vif.update_sw_rst_req(sw_rst_from_rstmgr);
      if (ndm_reset) send_ndm_reset();

      // Expect to start reset.
      `DV_WAIT(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive)
      `uvm_info(`gfn, "Started to process reset", UVM_MEDIUM)

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from reset", UVM_MEDIUM)

      check_wake_info(.reasons('0), .fall_through(1'b0), .abort(1'b0));

      cfg.slow_clk_rst_vif.wait_clks(4);
      check_reset_status('0);

      // And check interrupt is not set.
      check_and_clear_interrupt(.expected(1'b0));
    end
    clear_wake_info();
  endtask

endclass : pwrmgr_reset_vseq
