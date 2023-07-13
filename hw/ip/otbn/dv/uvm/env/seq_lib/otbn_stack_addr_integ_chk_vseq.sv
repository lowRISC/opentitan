// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) OTBN.*_STACK.ADDR.INTEGRITY

class otbn_stack_addr_integ_chk_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_stack_addr_integ_chk_vseq)
  `uvm_object_new

  bit end_test;

  task body();
    do_end_addr_check = 0;
    fork
      begin
        super.body();
      end
      begin
        inject_integ_err();
      end
    join
  endtask: body

  task inject_integ_err();
    bit err_type;
    string err_path;
    string top_valid_path;
    string stack_read_path;
    string stack_wr_idx_path;
    string stack_write_path;
    bit stack_write;
    bit top_valid;
    bit stack_read;
    bit [31:0] err_val = 32'd1 << 20;
    `DV_CHECK_STD_RANDOMIZE_FATAL(err_type)
    if (err_type) begin // err_type = 1 -> call stack error injection
        top_valid_path = "tb.dut.u_otbn_core.u_otbn_rf_base.u_call_stack.top_valid_o";
        stack_wr_idx_path = "tb.dut.u_otbn_core.u_otbn_rf_base.u_call_stack.stack_wr_idx";
        stack_read_path =
        "tb.dut.u_otbn_core.u_otbn_instruction_fetch.ctrl_flow_predec_o.call_stack_pop";
        stack_write_path = "tb.dut.u_otbn_core.u_otbn_rf_base.u_call_stack.stack_write_o";
    end else begin //  err_type = 0 -> loop stack error injection
        top_valid_path =
    "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack.top_valid_o";
        stack_wr_idx_path =
    "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack.stack_wr_idx[2:0]";
        stack_read_path =
    "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack.stack_read_o";
        stack_write_path =
    "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack.stack_write";
    end
    `DV_SPINWAIT(
      do begin
        @(cfg.clk_rst_vif.cb);
        `DV_CHECK_FATAL(uvm_hdl_read(top_valid_path, top_valid));
      end while (!top_valid);
    )
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
    `DV_CHECK_FATAL(uvm_hdl_read(top_valid_path, top_valid));
    if (top_valid) begin
      fork
        begin: isolation_fork
          fork
            begin
              if (err_type) begin
                `DV_SPINWAIT(
                  do begin
                    @(cfg.clk_rst_vif.cb);
                    `DV_CHECK_FATAL(uvm_hdl_read(stack_read_path, stack_read));
                  end while (!stack_read);
                )
                cfg.model_agent_cfg.vif.send_err_escalation(err_val);
              end else begin
                // error is injected in the corrupt_stack task.
                // We wait here till the otbn is locked so that we don't exit the fork early.
                `DV_WAIT(end_test)
                @(cfg.clk_rst_vif.cb);
              end
            end
            begin
              corrupt_stack(stack_wr_idx_path, err_type, err_path);
              forever begin
                `DV_SPINWAIT(
                  do begin
                    @(cfg.clk_rst_vif.cb);
                    `DV_CHECK_FATAL(uvm_hdl_read(stack_write_path, stack_write));
                  end while (!stack_write);
                )
                @(cfg.clk_rst_vif.cb);
                corrupt_stack(stack_wr_idx_path, err_type, err_path);
              end // forever begin
            end // fork begin
          join_any
          disable fork;
        end: isolation_fork
      join
      `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
      `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1);
      reset_if_locked();
    end
  endtask: inject_integ_err

  task corrupt_stack(string stack_wr_idx_path, bit err_type, output string err_path);
    bit [2:0] stack_wr_idx;
    bit [38:0] good_data;
    bit [38:0] bad_data;
    bit [31:0] mask;
    bit [31:0] err_val = 32'd1 << 20;
    `DV_CHECK_FATAL(uvm_hdl_read(stack_wr_idx_path, stack_wr_idx));
    if (stack_wr_idx != 0) begin
      if (err_type) begin
        $sformat(err_path, "tb.dut.u_otbn_core.u_otbn_rf_base.u_call_stack.stack_storage[%0d]",
                 (stack_wr_idx-1));
      end else begin
        `DV_CHECK_FATAL(uvm_hdl_read(stack_wr_idx_path, stack_wr_idx));
        $sformat(err_path,
    "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller.loop_info_stack.stack_storage[%0d]"
                 , (stack_wr_idx - 1));
      end
      `DV_CHECK_FATAL(uvm_hdl_read(err_path, good_data));
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
      bad_data = good_data ^ mask;
      `DV_CHECK_FATAL(uvm_hdl_force(err_path, bad_data))
      if (!err_type) begin
        cfg.model_agent_cfg.vif.send_err_escalation(err_val);
        `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
        end_test = 1;
      end
    end
  endtask: corrupt_stack
endclass : otbn_stack_addr_integ_chk_vseq
