// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to verify the countermeasure(s) OTBN.*_STACK.ADDR.INTEGRITY.

class otbn_stack_addr_integ_chk_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_stack_addr_integ_chk_vseq)
  `uvm_object_new

  bit end_test;

  task body();
    do_end_addr_check = 0;
    fork
      super.body();
      inject_integ_err();
    join
  endtask: body

  // Wait until the value at path is nonzero or until OTBN finishes execution.
  //
  // This process is safe to kill at any time, because it doesn't start any TL transactions.
  task wait_for_flag(string path);
    fork begin : isolation_fork
      fork
        // This is the main process, which repeatedly reads the value at path and completes if the
        // values becomes nonzero.
        begin
          uvm_hdl_data_t value = 0;
          `DV_SPINWAIT(do begin
                       @(cfg.clk_rst_vif.cb);
                       `DV_CHECK_FATAL(uvm_hdl_read(path, value));
                       end while (!value);)
        end
        // This process waits until OTBN completes execution or until reset. Passing backdoor=1
        // ensures that we won't start any TL reads of the status register.
        wait_for_run_completion(.verbosity(UVM_HIGH), .backdoor(1'b1));

      join_any
      disable fork;
    end join
  endtask

  // Wait until a short time after stack path becomes nonempty, then wait a short time. If it is
  // still nonempty, write 1 to still_nonzero.
  task wait_until_after_nonempty(input string stack_path, output bit still_nonzero);
    string top_valid_path = {stack_path, ".top_valid_o"};
    logic  top_valid;

    // Wait until the stack is nonempty
    wait_for_flag(top_valid_path);

    // Now wait a short time more (to avoid triggering just after the stack is first written to)
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // Check again to see whether the stack is nonempty. Hopefully it is (if not, we give up)
    `DV_CHECK_FATAL(uvm_hdl_read(top_valid_path, top_valid));
    still_nonzero = (top_valid != 0);
  endtask

  task send_escalation_to_model();
    `uvm_info(`gfn, "Telling model agent to take an error escalation", UVM_MEDIUM)
    cfg.model_agent_cfg.vif.send_err_escalation(32'd1 << 20);
  endtask

  task wait_for_call_stack_read(string rf_base_path);
    wait_for_flag({rf_base_path, ".pop_stack_reqd"});
  endtask

  task inject_integ_err();
    string       base_path, stack_path;
    bit          stack_nonempty;
    int unsigned msb;
    string       forced_paths[$];

    // This flag chooses whether we inject an error into the call stack (err_type=1) or the loop
    // stack (err_type=0).
    bit err_type = $urandom_range(0, 1);

    if (err_type) begin
      // We want to inject an error into the call stack (the data backing x1)
      base_path = "tb.dut.u_otbn_core.u_otbn_rf_base";
      stack_path = {base_path, ".u_call_stack"};
      msb = 38;
    end else begin
      // We want to inject an error into the loop stack
      base_path = "tb.dut.u_otbn_core.u_otbn_controller.u_otbn_loop_controller";
      stack_path = {base_path, ".loop_info_stack"};
      msb = 34;
    end

    wait_until_after_nonempty(stack_path, stack_nonempty);
    // Looks like the stack emptied again. Give up.
    if (!stack_nonempty) return;

    fork begin: isolation_fork
      fork
        // This process injects an error by corrupting every value just after the RTL has written it
        // to the stack. We expect the RTL to detect the error when it reads the value back out
        // again.
        begin
          corrupt_stack(stack_path, err_type == 0, msb, forced_paths);
          forever begin
            wait_for_flag({stack_path, ".stack_write_o"});
            @(cfg.clk_rst_vif.cb);
            corrupt_stack(stack_path, err_type == 0, msb, forced_paths);
          end
        end

        // Wait until the next read of the stack. We know that we are corrupting every value written
        // into the stack, so we expect the RTL to detect an error as soon as we read something back
        // out again.
        begin
          if (err_type) begin
            // We have just injected an error into the call stack. Wait until it gets read back
            // again and then tell the model about the expected error.
            wait_for_call_stack_read(base_path);
            send_escalation_to_model();
          end else begin
            // A loop stack corruption should actually have become visible immediately, so we do the
            // short bit of waiting at the end of corrupt_stack. Wait here until that task has
            // finished, to avoid exiting the fork early.
            `DV_WAIT(end_test)
            @(cfg.clk_rst_vif.cb);
          end
        end

      join_any
      disable fork;
    end: isolation_fork
    join
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
    foreach (forced_paths[i]) begin
      `DV_CHECK_FATAL(uvm_hdl_release(forced_paths[i]) == 1);
    end
    reset_if_locked();
  endtask: inject_integ_err

  // Corrupt a value at path by XOR'ing with a value that has 1 or 2 bits set and forcing the
  // resulting value. The msb argument gives the index of the MSB of the variable value that is
  // being forced.
  task corrupt_at_path(string path, int unsigned msb);
    bit [38:0] mask;
    bit [38:0] good_data, bad_data;

    `DV_CHECK_FATAL(msb <= 38);

    `DV_CHECK_FATAL(uvm_hdl_read(path, good_data));
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask,
                                       $countones(mask) inside {[1:2]};
                                       mask >> (msb + 1) == 0;)
    bad_data = good_data ^ mask;

    `uvm_info(`gfn,
              $sformatf({"Corrupting stack entry:\n",
                         "  path = %0s.\n",
                         "  %10x -> %10x"},
                        path, good_data, bad_data),
              UVM_MEDIUM)

    `DV_CHECK_FATAL(uvm_hdl_force(path, bad_data));
  endtask

  // Corrupt the top of the stack.
  //
  // This uses uvm_hdl_force to force the signal and writes the path of each value forced to
  // forced_path (to be released by the caller).
  //
  // If immediately_escalate is true, send an error escalation to the model immediately and then
  // wait until it locks itself.
  //
  // MSB gives the msb of the stack elements (at most 38 is supported).
  task corrupt_stack(string       stack_path,
                     bit          immediately_escalate,
                     int unsigned msb,
                     string       forced_paths[$]);
    string    err_path;
    bit [2:0] stack_wr_idx;
    string    stack_wr_idx_path = {stack_path, ".stack_wr_idx"};

    // Read the write index for the stack. If the write index happens to be zero then the stack must
    // be empty. Exit without doing anything.
    `DV_CHECK_FATAL(uvm_hdl_read(stack_wr_idx_path, stack_wr_idx));
    if (stack_wr_idx == 0) return;

    // If the write index is positive, the top value that has been written should be at position
    // stack_wr_idx - 1.
    $sformat(err_path, "%s.stack_storage[%0d]", stack_path, stack_wr_idx - 1);

    corrupt_at_path(err_path, msb);

    forced_paths.push_back(err_path);

    if (immediately_escalate) begin
      // When immediately_escalate is true, we assume that the corruption we have just introduced
      // will be visible through the top_data_o port from otbn_stack. This is almost immediate, but
      // the index of the element to be exposed is computed from stack_rd_idx which might be a cycle
      // behind the "correct" value that we have calculated from stack_wr_idx.
      //
      // The element index gets updated when stack_wr_ptr_commit is true. If that is the case,
      // mirror the delay by waiting an extra cycle before sending the escalation to the model.
      logic  stack_wr_ptr_commit;
      string commit_path = {stack_path, ".stack_wr_ptr_commit"};
      `DV_CHECK_FATAL(uvm_hdl_read(commit_path, stack_wr_ptr_commit))
      if (stack_wr_ptr_commit) begin
        @(cfg.clk_rst_vif.cb);
      end

      send_escalation_to_model();
      `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
      end_test = 1;
    end
  endtask: corrupt_stack
endclass : otbn_stack_addr_integ_chk_vseq
