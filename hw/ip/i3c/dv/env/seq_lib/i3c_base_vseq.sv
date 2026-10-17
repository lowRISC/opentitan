// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i3c_base_vseq extends cip_base_vseq #(
    .RAL_T               (i3c_reg_block),
    .CFG_T               (i3c_env_cfg),
    .COV_T               (i3c_env_cov),
    .VIRTUAL_SEQUENCER_T (i3c_virtual_sequencer)
  );
  `uvm_object_utils(i3c_base_vseq)

  `uvm_object_new

  // Reset the AON domain together with the main domain, so that the registers of both domains
  // return to their reset values.
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD") begin
        // Keep the AON domain in reset until the main domain leaves reset.
        cfg.clk_aon_rst_vif.drive_rst_pin(0);
        cfg.clk_aon_rst_vif.apply_reset(.reset_width_clks($urandom_range(2, 5)));
      end
      super.apply_reset(kind);
    join
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(max2(reset_duration_ps, cfg.clk_aon_rst_vif.clk_period_ps));
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
  endtask

  virtual task wait_for_reset(string reset_kind     = "HARD",
                              bit wait_for_assert   = 1,
                              bit wait_for_deassert = 1);
    fork
      super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
      if (reset_kind == "HARD") begin
        if (wait_for_assert) begin
          `uvm_info(`gfn, "waiting for rst_aon_n assertion...", UVM_MEDIUM)
          @(negedge cfg.clk_aon_rst_vif.rst_n);
        end
        if (wait_for_deassert) begin
          `uvm_info(`gfn, "waiting for rst_aon_n de-assertion...", UVM_MEDIUM)
          @(posedge cfg.clk_aon_rst_vif.rst_n);
        end
      end
    join
  endtask

endclass : i3c_base_vseq
