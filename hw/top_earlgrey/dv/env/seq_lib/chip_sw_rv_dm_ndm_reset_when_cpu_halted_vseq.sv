// Copyright lowRISC contributors (OpenTitan project).
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
    bit ready;
    uvm_reg_data_t rw_data;
    abstract_cmd_err_e status;
    logic [31:0] cmd_data[$];

    super.body();

    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == "Ready for CPU halt request",
             "Timed out waiting for the CPU to be ready for a halt request.")
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    cfg.debugger.set_dmactive(1);
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    // Verify the CPU is running (and the JTAG interface is alive) before asserting haltreq.
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 1)
    cfg.debugger.set_haltreq(1);
    cfg.debugger.wait_cpu_halted();

    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 1)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.anyrunning, rw_data), 0)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allrunning, rw_data), 0)
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 1000));

    cfg.debugger.set_haltreq(0);
    cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1000, 10000));
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data), .blocking(1));
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data), 1)

    // Ensure the dm is ready for abstract commands.
    cfg.debugger.abstract_cmd_dm_ready(ready);
    `DV_CHECK(ready)

    // Read all general purpose registers.
    cfg.debugger.abstract_cmd_reg_read(.regno('h1000), .value_q(cmd_data), .status(status),
                                       .size(16));
    `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
    foreach (cmd_data[i]) begin
      `uvm_info(`gfn, $sformatf("Read by the debugger: GPR[%0d] = 0x%0h", i, cmd_data[i]), UVM_LOW)
      // TODO: most GPR values match with the probed value. But some are actively used by the CPU.
      // Commenting out this check for now - figure out if the in-use GPRs are fixed. If they are,
      // we can just skip those.
      // `DV_CHECK_EQ(cmd_data[i], cfg.chip_vif.probed_cpu_csrs.gprs[i])
    end

    // Read DCSR and verify the cause field.
    cmd_data = '{};
    cfg.debugger.abstract_cmd_reg_read(.regno(jtag_rv_debugger_pkg::RvCoreCsrDcsr),
                                       .value_q(cmd_data), .status(status));
    `DV_CHECK_EQ(status, jtag_rv_debugger_pkg::AbstractCmdErrNone)
    `uvm_info(`gfn, $sformatf("Read by the debugger: DCSR = 0x%0h", cmd_data[0]), UVM_LOW)
    `DV_CHECK_EQ(cmd_data[0], cfg.chip_vif.probed_cpu_csrs.dcsr)
    `DV_CHECK_EQ(cfg.chip_vif.probed_cpu_csrs.dcsr.cause, jtag_rv_debugger_pkg::RvDebugCauseHaltReq)

    // Read some chip CSRs over SBA. Arbitrarily chose LC ctrl device ID which can be checked for
    // correctness via backdoor.
    begin
      otp_ctrl_pkg::otp_device_id_t device_id_act;
      otp_ctrl_pkg::otp_device_id_t device_id_exp;

      for (int i = 0; i < otp_ctrl_pkg::DeviceIdWidth / 32; i++) begin
        csr_rd(.ptr(ral.lc_ctrl_regs.device_id[i]), .value(device_id_act[i*32+:32]), .blocking(1),
               .user_ftdr(cfg.debugger.m_sba_access_reg_frontdoor));
        device_id_exp[i*32+:32] = cfg.mem_bkdr_util_h[Otp].read32(
            otp_ctrl_reg_pkg::DeviceIdOffset + i * 4);
      end
      `DV_CHECK_EQ(device_id_act, device_id_exp)
    end

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
