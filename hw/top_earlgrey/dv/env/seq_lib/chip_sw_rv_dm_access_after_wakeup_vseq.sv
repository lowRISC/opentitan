// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rv_dm_access_after_wakeup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_dm_access_after_wakeup_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Release power button.
    cfg.chip_vif.pwrb_in_if.drive(1'b1);
  endtask : pre_start

  task activate_jtag_dmi();
    // Set up JTAG RV_DM TAP.
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    // Wait a few clocks for the strap change to take effect before driving the JTAG interface
    cfg.clk_rst_vif.wait_clks(5);

    // Attempt to activate RV_DM via JTAG.
    csr_wr(.ptr(cfg.jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    cfg.clk_rst_vif.wait_clks(5);
  endtask : activate_jtag_dmi

  virtual task body();
    uint           timeout_long       = 10_000_000;
    uint           timeout_short      = 1_000_000;
    bit [7:0]      software_barrier[] = '{0};
    uvm_reg_data_t exp_data = $urandom();

    super.body();

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Software Setup.");,
                 "Timed out waiting for software setup.", timeout_long)

    activate_jtag_dmi();
    csr_wr(
      .ptr(cfg.jtag_dmi_ral.progbuf[0]),
      .value(exp_data),
      .path(UVM_FRONTDOOR));
    csr_rd_check(
      .ptr(cfg.jtag_dmi_ral.progbuf[0]),
      .compare_value(exp_data),
      .path(UVM_FRONTDOOR),
      .err_msg("straight after write."));

    // Allow the software to continue execution.
    software_barrier[0] = 1;
    `uvm_info(`gfn, "SoftwareBarrier = 1", UVM_LOW)
    sw_symbol_backdoor_overwrite("kSoftwareBarrier", software_barrier);

    // Wait for the software to fall asleep.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Entering normal sleep.");,
                 "Timed out waiting for device to enter normal sleep.", timeout_short)

    // Press the power button to wake up the device.
    `uvm_info(`gfn, "Pushing power button.", UVM_LOW)
    cfg.chip_vif.pwrb_in_if.drive(1'b0); // pressing power button

    // Wait for the software to wake up.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Waking up from normal sleep.");,
                 "Timed out waiting for device to wakeup from normal sleep.", timeout_short)

    `uvm_info(`gfn, "Releasing power button.", UVM_LOW)
    cfg.chip_vif.pwrb_in_if.drive(1'b1); // releasing power button

    // Check the program buffer retained the expected value after a normal
    // sleep.
    csr_rd_check(
      .ptr(cfg.jtag_dmi_ral.progbuf[0]),
      .compare_value(exp_data),
      .path(UVM_FRONTDOOR),
      .err_msg("after normal sleep."));

    // Allow the software to continue execution.
    software_barrier[0] = 2;
    `uvm_info(`gfn, "SoftwareBarrier = 2", UVM_LOW)
    sw_symbol_backdoor_overwrite("kSoftwareBarrier", software_barrier);


    // Wait for the software to fall asleep.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Entering deep sleep.");,
                 "Timed out waiting for device to enter deep sleep.", timeout_short)

    // Press the power button to wake up the device.
    `uvm_info(`gfn, "Pushing power button.", UVM_LOW)
    cfg.chip_vif.pwrb_in_if.drive(1'b0); // pressing power button

    // Wait for the software to wake up.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Waking up from deep sleep.");,
                 "Timed out waiting for device to wakeup from deep sleep.", timeout_long)

    `uvm_info(`gfn, "Releasing power button.", UVM_LOW)
    cfg.chip_vif.pwrb_in_if.drive(1'b1); // releasing power button

    // We must reset the agent side also to stay synchronized with the design
    cfg.m_jtag_riscv_agent_cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
    // Wait for JTAG agent to come out of reset
    cfg.clk_rst_vif.wait_clks(5);
    // Reactivate DMI
    activate_jtag_dmi();
    exp_data = $urandom();
    csr_wr(
      .ptr(cfg.jtag_dmi_ral.progbuf[0]),
      .value(exp_data),
      .path(UVM_FRONTDOOR));
    csr_rd_check(
      .ptr(cfg.jtag_dmi_ral.progbuf[0]),
      .compare_value(exp_data),
      .path(UVM_FRONTDOOR),
      .err_msg("after deep sleep."));

    // Allow the software to continue execution.
    software_barrier[0] = 3;
    `uvm_info(`gfn, "SoftwareBarrier = 3", UVM_LOW)
    sw_symbol_backdoor_overwrite("kSoftwareBarrier", software_barrier);

  endtask : body

endclass : chip_sw_rv_dm_access_after_wakeup_vseq
