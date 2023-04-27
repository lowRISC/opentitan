// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies that the debug resources are accessible before and after a HW reset event due to
// alert escalation.
//
// This test reuses the same SW test as chip_sw_alert_handler_escalation test. The SV portion of the
// SW test does different things. For this test, the SV side verifies the accessibility the JTAG DMI
// space via JTAG before, during and after escalation reset reboot.
class chip_sw_rv_dm_access_after_escalation_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_dm_access_after_escalation_reset_vseq)
  `uvm_object_new

  bit pause_jtag_dmi_ral_csr_rw_seq;
  bit jtag_dmi_ral_csr_rw_seq_busy;

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
    max_outstanding_accesses = 1;
  endtask

  virtual task body();
    super.body();

    `uvm_info(`gfn, "Waiting for HW debug to be enabled", UVM_MEDIUM)
    `DV_WAIT(cfg.chip_vif.pinmux_lc_hw_debug_en)
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(10);

    `uvm_info(`gfn, "Activating the debug module", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    fork run_jtag_dmi_ral_csr_rw_seq(); join_none

    // These checkpoints ensure SW is progressing through the escalation stages.
    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == "Keymgr entered Init State")
    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == "You are experiencing an NMI")
    pause_jtag_dmi_ral_csr_rw_seq = 1;

    `uvm_info(`gfn, "Waiting for escalation reset to complete", UVM_MEDIUM)
    `DV_WAIT(!cfg.chip_vif.pinmux_lc_hw_debug_en)
    // The JTAG CSR access sequence must have stopped by now, or else we will have issues.
    `DV_CHECK_FATAL(!jtag_dmi_ral_csr_rw_seq_busy)

    fork
      // The escalation reset will reset the debug module. The JTAG agent needs to also be reset.
      cfg.m_jtag_riscv_agent_cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
      `DV_WAIT(cfg.chip_vif.pinmux_lc_hw_debug_en)
    join

    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(10);
    `uvm_info(`gfn, "Activating the debug module again after escalation reset", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    pause_jtag_dmi_ral_csr_rw_seq = 0;

    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == "Reset due to alert escalation")
    pause_jtag_dmi_ral_csr_rw_seq = 1;
    `DV_WAIT(!jtag_dmi_ral_csr_rw_seq_busy)
  endtask

  // Run the CSR RW sequence on jtag_dmi_ral.
  //
  // A forever running thread which continuously accesses the JTAG DMI space, with exclusions
  // factored in. Execution can be paused temporarily with pause_jtag_dmi_ral_csr_rw_seq signal.
  virtual task run_jtag_dmi_ral_csr_rw_seq();
    csr_rw_seq m_csr_seq = csr_rw_seq::type_id::create("m_csr_seq");
    csr_excl_item csr_excl = csr_utils_pkg::get_excl_item(jtag_dmi_ral);
    m_csr_seq.models = {jtag_dmi_ral};
    if (csr_excl != null) csr_excl.print_exclusions();
    forever begin
      if (pause_jtag_dmi_ral_csr_rw_seq) wait (!pause_jtag_dmi_ral_csr_rw_seq);
      `uvm_info(`gfn, "Running JTAG DMI RAL CSR rw seq", UVM_MEDIUM)
      jtag_dmi_ral_csr_rw_seq_busy = 1;
      m_csr_seq.start(null);
      jtag_dmi_ral_csr_rw_seq_busy = 0;
    end
  endtask

endclass
