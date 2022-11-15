// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies that an NDM reset request after the CPU has been halted resets the original haltreq.
class chip_sw_rv_dm_ndm_reset_when_cpu_halted_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_dm_ndm_reset_when_cpu_halted_vseq)
  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    super.pre_start();
  endtask

  virtual task body();
    bit rebooted;
    uvm_reg_data_t rw_data;
    super.body();

    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == "Ready for CPU halt request",
             "Timed out waiting for the CPU to be ready for a halt request.")
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    `uvm_info(`gfn, "Activating the debug module", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 1)

    `uvm_info(`gfn, "Asserting CPU haltreq", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1), .blocking(1), .predict(1));

    `uvm_info(`gfn, "Waiting for CPU halted", UVM_MEDIUM)
    `DV_SPINWAIT(
      do begin
        csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
      end while (dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data) == 0);
    )
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 0)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 0)
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    `uvm_info(`gfn, "De-asserting CPU haltreq since CPU is halted", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(0), .blocking(1), .predict(1));
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1000, 10000));
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 1)

    // TODO: Execute abstract command to read DCSR and verify the cause field.

    `uvm_info(`gfn, "Issuing an NDM reset request", UVM_MEDIUM)
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(1), .blocking(1), .predict(1));

    fork
      begin
        cfg.chip_vif.aon_clk_por_rst_if.wait_clks($urandom_range(5, 20));
        `uvm_info(`gfn, "Clearing the NDM reset request", UVM_MEDIUM)
        // If we do not clear the ndm reset req, it will result in reboot loop.
        csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0), .blocking(1), .predict(1));
      end
      begin
        `uvm_info(`gfn, "Verifying the CPU halted state is cleared", UVM_MEDIUM)
        `DV_SPINWAIT(
          do begin
            csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
          end while (dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data) == 1);
        )
        `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data), 0)
        `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 0)
        `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 1)
        `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 1)

        `uvm_info(`gfn, "Continuing to read dmstatus CSR through NDM reset", UVM_LOW)
        // This proves that the debugger can access the debug resources while the NDM reset is
        // ongoing, and there are no lockups elsewhere.
        while (!rebooted) begin
          csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
          `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data), 0)
          `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 0)
          `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 1)
          `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 1)
        end
      end
      begin
        `uvm_info(`gfn, "Waiting for NDM reset to complete", UVM_MEDIUM)
        `DV_WAIT(!cfg.chip_vif.lc_ready)
        `DV_WAIT(cfg.chip_vif.lc_ready)
        cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);
        rebooted = 1;
      end
    join

    // Let the CPU SW run its course (second reset phase after NDM reset).
  endtask

endclass
