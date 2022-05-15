// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_common_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        csr_rd_check(.ptr(ral.fatal_err_code.idle_cnt), .compare_value(1));
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unexpected sec_cm_type %0s", if_proxy.sec_cm_type.name))
      end
    endcase
  endtask

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
      return;
    end
    if (if_proxy.sec_cm_type == SecCmPrimCount) begin
      $assertoff(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
    end
  endfunction

  task initialize_on_start();
    super.initialize_on_start();
    // update default idle to false for
    // csr test.
    cfg.clkmgr_vif.idle_i = {NUM_TRANS{MuBi4False}};
  endtask : initialize_on_start

  // this is used for non-main clock registers.
  // to compensate clock difference, wait longer until
  // see get_alert()
  task skid_check_fatal_alert_nonblocking(string alert_name);     
    fork
      `DV_SPINWAIT_EXIT(
          forever begin
            // 1 extra cycle to make sure no race condition
            repeat (alert_esc_agent_pkg::ALERT_B2B_DELAY + 20) begin
              cfg.clk_rst_vif.wait_n_clks(1);
              if (cfg.m_alert_agent_cfg[alert_name].vif.get_alert() == 1) break;
            end
            `DV_CHECK_EQ(cfg.m_alert_agent_cfg[alert_name].vif.get_alert(), 1,
                         $sformatf("fatal error %0s does not trigger!", alert_name))
            cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();
          end,
          wait(cfg.under_reset);)
    join_none
  endtask
  
  // override shadow_reg_errors task
  // to cover shadow regs under clock div2, div4
  task shadow_reg_errors_check_fatal_alert_nonblocking(dv_base_reg shadowed_csr, string alert_name);
    bit use_skid_chk = 0;
     
    // Add delay to reach sampling point (tb.dut.u_reg.shadowed_storage_err_o)
    // from current time 
    if (shadowed_csr.get_name() == "io_div2_meas_ctrl_shadowed" ||
	shadowed_csr.get_name() == "usb_meas_ctrl_shadowed" ||
	shadowed_csr.get_name() == "io_div4_meas_ctrl_shadowed") begin
       use_skid_chk = 1;
    end

    if (cfg.m_alert_agent_cfg.exists(alert_name)) begin
      // add clock cycle delay
      cfg.clk_rst_vif.wait_clks(3);
       $display("%t:JDONDBG",$time);
       
      if (use_skid_chk == 1) begin
	 skid_check_fatal_alert_nonblocking(alert_name);	 
      end else begin
	 check_fatal_alert_nonblocking(alert_name);
      end
    end
  endtask

endclass
