// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The regwen vseq attempts to write to registers whose regwen is randomly on or off to check
// the register contents is not updated when off. More details in the clkmgr_testplan.hjson file.
class clkmgr_regwen_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_regwen_vseq)

  `uvm_object_new

  task check_extclk_regwen();
    bit enable;
    int prev_value;
    int new_value = {extclk_ctrl_high_speed_sel, extclk_ctrl_sel};
    `DV_CHECK_STD_RANDOMIZE_FATAL(enable)
    `uvm_info(`gfn, $sformatf("Check extclk_ctrl regwen set to %b begin", enable), UVM_MEDIUM)
    csr_wr(.ptr(ral.extclk_ctrl_regwen), .value(enable));
    csr_rd(.ptr(ral.extclk_ctrl), .value(prev_value));
    csr_wr(.ptr(ral.extclk_ctrl), .value(new_value));
    csr_rd_check(.ptr(ral.extclk_ctrl), .compare_value(enable ? new_value : prev_value));
    `uvm_info(`gfn, "Check extclk_ctrl regwen end", UVM_MEDIUM)
  endtask : check_extclk_regwen

  // This must be careful to turn measurements off right after checking the updates
  // to avoid measurement errors. We could set the thresholds correctly, but we
  // might as well set them randomly for good measure. Carefully masks only the
  // real bits for the comparison.
  task check_meas_ctrl_regwen();
    bit regwen_enable;
    `DV_CHECK_STD_RANDOMIZE_FATAL(regwen_enable)
    csr_wr(.ptr(ral.measure_ctrl_regwen), .value(regwen_enable));
    foreach (ExpectedCounts[clk]) begin
      clk_mesr_e clk_mesr = clk_mesr_e'(clk);
      uvm_reg ctrl_shadowed = meas_ctrl_regs[clk_mesr].ctrl_lo.get_dv_base_reg_parent();
      uvm_reg_data_t prev_en;
      mubi4_t new_en = get_rand_mubi4_val(1, 1, 2);
      int prev_ctrl;
      int new_ctrl = $urandom();
      int actual_ctrl;
      int lo_mask = ((1 << meas_ctrl_regs[clk_mesr].ctrl_lo.get_n_bits()) - 1) <<
                     meas_ctrl_regs[clk_mesr].ctrl_lo.get_lsb_pos();
      int hi_mask = ((1 << meas_ctrl_regs[clk_mesr].ctrl_hi.get_n_bits()) - 1) <<
                     meas_ctrl_regs[clk_mesr].ctrl_hi.get_lsb_pos();
      `uvm_info(`gfn, $sformatf(
                "Check %0s regwen set to %b begin", meas_ctrl_regs[clk_mesr].name, regwen_enable),
                UVM_MEDIUM)
      csr_rd(.ptr(meas_ctrl_regs[clk_mesr].en), .value(prev_en));
      csr_rd(.ptr(ctrl_shadowed), .value(prev_ctrl));
      csr_wr(.ptr(ctrl_shadowed), .value(new_ctrl));
      csr_wr(.ptr(meas_ctrl_regs[clk_mesr].en), .value(new_en));
      csr_rd_check(.ptr(meas_ctrl_regs[clk_mesr].en),
                   .compare_value(mubi4_t'(regwen_enable ? new_en : prev_en)));
      csr_rd_check(.ptr(ctrl_shadowed), .compare_value(regwen_enable ? new_ctrl : prev_ctrl),
                   .compare_mask(lo_mask | hi_mask));
      `uvm_info(`gfn, $sformatf("Check %0s regwen end", meas_ctrl_regs[clk_mesr].name),
                UVM_MEDIUM)
      csr_wr(.ptr(meas_ctrl_regs[clk_mesr].en), .value(MuBi4False));
    end
  endtask : check_meas_ctrl_regwen

  task body();
    // Make sure the aon clock is running as slow as it is meant to, otherwise the aon clock
    // runs fast enough that we could end up triggering faults due to the random settings for
    // the thresholds.
    cfg.aon_clk_rst_vif.set_freq_khz(AonClkHz / 1_000);

    `uvm_info(`gfn, $sformatf("Will run %0d rounds", num_trans), UVM_MEDIUM)
    for (int i = 0; i < num_trans; ++i) begin
      check_extclk_regwen();
      check_meas_ctrl_regwen();
      apply_reset("HARD");
      // This is to make sure we don't start writes immediately after reset,
      // otherwise the tl_agent could mistakenly consider the following read
      // happens during reset.
      cfg.clk_rst_vif.wait_clks(4);
      csr_rd_check(.ptr(ral.extclk_ctrl_regwen), .compare_value(1));
      csr_rd_check(.ptr(ral.measure_ctrl_regwen), .compare_value(1));
    end
  endtask : body

endclass : clkmgr_regwen_vseq
