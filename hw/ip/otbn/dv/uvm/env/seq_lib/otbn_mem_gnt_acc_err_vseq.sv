// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) PC.CTRL_FLOW.REDUN.

class otbn_mem_gnt_acc_err_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_mem_gnt_acc_err_vseq)
  `uvm_object_new

  task body();
    do_end_addr_check = 0;
    fork
      begin
        super.body();
      end
      begin
        inject_gnt_err();
      end
    join
  endtask: body

  task inject_gnt_err();
    bit req;
    bit choose_mem;
    string gnt_path;
    bit [31:0] err_val = 32'd1 << 20;

    `DV_CHECK_STD_RANDOMIZE_FATAL(choose_mem)
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
    `DV_ASSERT_CTRL_REQ("DMemAsserts", 0)
    case(choose_mem)
      0: begin // Dmem
        gnt_path = "tb.dut.u_dmem.gnt_o";
        `DV_SPINWAIT(
          do begin
            @(cfg.clk_rst_vif.cb);
            uvm_hdl_read("tb.dut.u_dmem.req_i", req);
          end while(!req);
        )
        `DV_CHECK_FATAL(uvm_hdl_force(gnt_path, 0) == 1)
      end
      1: begin // Imem
        gnt_path = "tb.dut.u_imem.gnt_o";
        `DV_SPINWAIT(
          do begin
            @(cfg.clk_rst_vif.cb);
            uvm_hdl_read("tb.dut.u_imem.req_i", req);
          end while(!req);
        )
        `DV_CHECK_FATAL(uvm_hdl_force(gnt_path, 0) == 1)
      end
      default: begin
        `uvm_fatal(`gfn, "randomization error")
      end
    endcase
      `uvm_info(`gfn, "injecting bad internal state error into ISS", UVM_HIGH)
      @(cfg.clk_rst_vif.cb);
      cfg.model_agent_cfg.vif.send_err_escalation(err_val);
      `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
      `DV_CHECK_FATAL(uvm_hdl_release(gnt_path) == 1);
      reset_if_locked();
      `DV_ASSERT_CTRL_REQ("DMemAsserts", 1)
  endtask: inject_gnt_err
endclass : otbn_mem_gnt_acc_err_vseq
