// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The reset test randomly introduces external resets, power glitches, and escalation resets.
class pwrmgr_reset_vseq extends pwrmgr_base_vseq;
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  `uvm_object_utils(pwrmgr_reset_vseq)

  `uvm_object_new

  rand bit power_glitch_reset;
  rand bit escalation_reset;

  // TODO(maturana) Enable escalation resets once there is support for driving them.
  constraint escalation_reset_c {escalation_reset == 1'b0;}
  constraint resets_en_c {
    solve resets, power_glitch_reset, escalation_reset before resets_en;
    |{resets_en & resets, power_glitch_reset, escalation_reset} == 1'b1;
  }

  constraint wakeups_c {wakeups == 0;}
  constraint wakeups_en_c {wakeups_en == 0;}

  prim_mubi_pkg::mubi4_t sw_rst_from_rstmgr;

  function void post_randomize();
    sw_rst_from_rstmgr = get_rand_mubi4_val(8, 4, 4);
    super.post_randomize();
  endfunction

  task body();
    logic [TL_DW-1:0] value;
    resets_t enabled_resets;

    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(0));
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, "Starting new round", UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      enabled_resets = resets_en & resets;
      `uvm_info(`gfn, $sformatf(
                "Enabled resets=0x%x, power_reset=%b, escalation=%b",
                enabled_resets,
                power_glitch_reset,
                escalation_reset
                ), UVM_MEDIUM)

      csr_wr(.ptr(ral.reset_en[0]), .value(resets_en));
      // This is necessary to propagate reset_en.
      wait_for_csr_to_propagate_to_slow_domain();

      // Trigger resets. The glitch is sent prior to the externals since if it is delayed
      // it will cause a separate reset after the externals, which complicates the checks.
      if (power_glitch_reset) begin
        `uvm_info(`gfn, "Sending power glitch", UVM_MEDIUM)
        cfg.pwrmgr_vif.glitch_power_reset();
      end
      cfg.clk_rst_vif.wait_clks(cycles_before_reset);
      `uvm_info(`gfn, $sformatf("Sending resets=0x%x", resets), UVM_MEDIUM)
      cfg.pwrmgr_vif.update_resets(resets);
      `uvm_info(`gfn, $sformatf("Sending sw reset from rstmgr=%b", sw_rst_from_rstmgr), UVM_MEDIUM)
      cfg.pwrmgr_vif.update_sw_rst_req(sw_rst_from_rstmgr);

      cfg.slow_clk_rst_vif.wait_clks(4);

      // This read is not always possible since the CPU may be off.
      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(enabled_resets),
                   .err_msg("failed reset_status check"));

      wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

      wait_for_fast_fsm_active();
      `uvm_info(`gfn, "Back from reset", UVM_MEDIUM)

      check_wake_info(.reasons('0), .fall_through(1'b0), .abort(1'b0));

      cfg.slow_clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.reset_status[0]), .compare_value('0));
    end
  endtask

endclass : pwrmgr_reset_vseq
