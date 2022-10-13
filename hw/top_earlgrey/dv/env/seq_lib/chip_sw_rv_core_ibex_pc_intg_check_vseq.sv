// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence that corrupts the PC and checks that an appropriate alert occurs.
class chip_sw_rv_core_ibex_pc_intg_check_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_core_ibex_pc_intg_check_vseq)

  `uvm_object_new

  virtual task body();
    string ibex_path, core_path, if_stage_path, glitch_path, instr_seq_path,
           alert_major_internal_path, fatal_hw_alert_path;
    int unsigned bit_idx;
    logic [31:0] orig_pc, glitch_mask, glitched_pc;
    logic exp_alert, alert_major_internal, fatal_hw_alert;

    super.body();

    // Wait until the CPU is executing code (and it starts in Boot ROM).
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)

    // Randomize the instant at which the glitch is injected.
    if ($urandom_range(1)) begin
      // Glitch at some time at which the CPU is in Boot ROM, which currently takes up to 18k CPU
      // clock cycles to execute.
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(18000));
    end else begin
      // Glitch after Boot ROM, when the CPU is executing program code.
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
      cfg.chip_vif.cpu_clk_rst_if.wait_n_clks($urandom_range(1000));
    end
    // Ensure we are still running.  If not, skip the test without injecting an error.
    if (!(cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusInBootRom,
                                                        SwTestStatusInTest})) begin
      `uvm_info(`gfn, "Skipping injection of error because CPU is not executing code.", UVM_LOW)
      return;
    end

    // Set path to the core and the PC to be glitched.
    ibex_path = "tb.dut.top_earlgrey.u_rv_core_ibex";
    core_path = $sformatf("%s.u_core.u_ibex_core", ibex_path);
    if_stage_path = $sformatf("%s.if_stage_i", core_path);
    glitch_path = $sformatf("%s.pc_if_o", if_stage_path);

    // Sample PC value prior to glitching.
    `DV_CHECK_FATAL(uvm_hdl_read(glitch_path, orig_pc))

    // Pick one bit in the PC and glitch it.
    bit_idx = $urandom_range(31);
    glitch_mask = 1 << bit_idx;
    glitched_pc = orig_pc ^ glitch_mask;

    // Force the glitched value onto the PC.
    `DV_CHECK_FATAL(uvm_hdl_force(glitch_path, glitched_pc));
    `uvm_info(`gfn, $sformatf("Forcing %s to value 'h%0x.", glitch_path, glitched_pc), UVM_LOW)

    // The check will only fire if the current instruction is a sequential one.  Depending on that
    // we expect an alert or we don't.
    instr_seq_path = $sformatf("%s.g_secure_pc.prev_instr_seq_q", if_stage_path);
    `DV_CHECK_FATAL(uvm_hdl_read(instr_seq_path, exp_alert))
    `ASSERT_I(ExpAlertMajorInternalKnown_A, !$isunknown(exp_alert))

    // Schedule DUT signal updates, so the DUT can react to the forced value.
    #1step;

    // Check that the alert matches our expectation.
    alert_major_internal_path = $sformatf("%s.alert_major_internal_o", core_path);
    `DV_CHECK_FATAL(uvm_hdl_read(alert_major_internal_path, alert_major_internal))
    `DV_CHECK_EQ_FATAL(alert_major_internal, exp_alert, "Major alert did not match expectation!")

    // Wait one cycle for the alert to propagate through the alert sender.
    cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(1);

    // Check if a fatal alert is sent out of rv_core_ibex.
    fatal_hw_alert_path = $sformatf("%s.alert_tx_o[2].alert_p", ibex_path);
    `DV_CHECK_FATAL(uvm_hdl_read(fatal_hw_alert_path, fatal_hw_alert))
    `DV_CHECK_EQ_FATAL(fatal_hw_alert, exp_alert, "Fatal HW alert did not match expectation!")

    // Release glitch.
    `DV_CHECK_FATAL(uvm_hdl_release(glitch_path));
    `uvm_info(`gfn, $sformatf("Releasing force of %s.", glitch_path), UVM_LOW)

    // Complete the test at this point because the program running on Ibex will not finish.
    dv_test_status_pkg::dv_test_status(1); // Test passed.
    $finish();
  endtask

endclass
