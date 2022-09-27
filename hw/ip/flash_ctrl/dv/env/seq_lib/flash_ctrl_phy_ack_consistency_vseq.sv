// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test triggers tb.dut.u_eflash.gen_flash_cores[0].u_core.spurious_ack_o
// by force.
class flash_ctrl_phy_ack_consistency_vseq extends flash_ctrl_phy_host_grant_err_vseq;
  `uvm_object_utils(flash_ctrl_phy_ack_consistency_vseq)
  `uvm_object_new

  task run_error_event();
    int delay;
    bit add_err1, add_err2;
    string path1 = "tb.dut.u_eflash.gen_flash_cores[0].u_core.ctrl_rsp_vld";
    string path2 = "tb.dut.u_eflash.gen_flash_cores[0].u_core.host_req_done_o";

    cfg.scb_h.exp_alert["fatal_err"] = 1;
    cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    repeat (2) begin
      // unit 100 ns;
      delay = $urandom_range(1, 10);
      #(delay * 100ns);

      if (add_err1) begin
        `DV_CHECK(uvm_hdl_release(path1))
      end
      if (add_err2) begin
        `DV_CHECK(uvm_hdl_release(path2))
      end

      if (add_err1 == 0 && add_err2 == 0) begin
        randcase
          1: begin
            add_err1 = 1;
            @(posedge cfg.flash_ctrl_vif.ctrl_fsm_idle);
            `DV_CHECK(uvm_hdl_force(path1, 1))
          end
          1: begin
            add_err2 = 1;
            wait(cfg.flash_ctrl_vif.host_outstanding == 0);
            `DV_CHECK(uvm_hdl_force(path2, 1))
          end
        endcase // randcase
      end
    end // repeat (2)
    check_fault(ral.fault_status.spurious_ack);
  endtask
endclass
