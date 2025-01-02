// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// readback_err_vseq
class sram_ctrl_readback_err_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_readback_err_vseq)

  `uvm_object_new

  // Indicates the number of memory accesses to be performed in this test.
  rand int num_ops;

  // Indicates at which memory access the fault is injected.
  rand int do_fi_op;

  constraint num_ops_c {
    num_ops inside {[10 : 200]};
  }

  constraint do_fi_op_c {
    do_fi_op inside {[10 : num_ops]};
  }

  int fi_iteration_position = 0;

  task drive_reqs(int iterations, bit write);
    // Perform random read/write operations.
    bit [TL_AW-1:0] addr;
    bit [TL_AW-1:0] sram_addr_mask = cfg.ral_models[cfg.sram_ral_name].get_addr_mask();
    bit [TL_AW-1:0] max_offset = {sram_addr_mask[TL_AW-1:2], 2'd0};
    logic [TL_DW-1:0] rdata;
    for (int iteration = 0; iteration < iterations; iteration++) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr, (addr & sram_addr_mask) < max_offset;)
        if (write) begin
          do_single_write(.addr(addr), .data(iteration + 1), .mask('1), .blocking(0));
        end else begin
          do_single_read(.addr(addr), .mask('1), .check_rdata(0), .blocking(0), .rdata(rdata));
        end
    end
  endtask

  task inject_fault(int iterations, int iteration_fi_position, string fi_path,
                    int fi_mask, string sram_req_path, string sram_we_path,
                    bit write_op, string alert_signal);
    // Inject a fault into the signal indicated by fi_path & monitor the response.
    bit req;
    int value;
    int value_faulty;
    for (int iteration = 0; iteration < iterations; iteration++) begin
      // Wait until the sram_we (for writes) or the sram_req (for reads) arrives.
      `DV_SPINWAIT(
        do begin
          cfg.clk_rst_vif.wait_n_clks(1);
          if (write_op) begin
            uvm_hdl_read(sram_we_path, req);
          end else begin
            uvm_hdl_read(sram_req_path, req);
          end
        end while(!req);
      )

      // Only inject if we reached the selected read/write transaction.
      if (iteration == iteration_fi_position) begin
        `uvm_info(`gfn, $sformatf(
                  "Injecting fault into %s in memory operation %d and check the %s alert",
                  fi_path, iteration_fi_position, alert_signal),
                  UVM_LOW)
        fork
          begin : inject_fault
            uvm_hdl_read(fi_path, value);
            value_faulty = value ^ fi_mask;
            `DV_CHECK(uvm_hdl_force(fi_path, value_faulty))
            // Release the faulty signal after one clock cycle.
            cfg.clk_rst_vif.wait_n_clks(1);
            `DV_CHECK(uvm_hdl_release(fi_path))
          end : inject_fault
          begin : monitor_response
            // Check if alert_signal was triggered.
            cfg.scb.set_exp_alert(alert_signal, .is_fatal(1'b1), .max_delay(20));
            wait_alert_trigger (alert_signal, .max_wait_cycle(20), .wait_complete(0));
            // Reset to get the DUT out of terminal state.
            apply_resets_concurrently();
          end : monitor_response
        join
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  task body();
    // Define the signal we are targeting to inject a fault. This list covers the
    // most relevant signals for SRAM read/write requests. The rdata signal for reads
    // is indirectly covered by the addr as a faulty address triggers the same behavior
    // as a faulted rdata.
    string fi_paths[3] = {"tb.dut.sram_addr", "tb.dut.sram_wdata", "tb.dut.sram_we"};
    int fi_masks[3] = {2, 2, 1};
    // These variables hold the randomly selected target signal.
    string fi_path;
    int fi_mask;
    // Used to keep track of the incoming TL-UL requests.
    string sram_req_path = "tb.dut.sram_req";
    // The readback feature raises the fatal_error alert on a mismatch.
    string alert_signal = "fatal_error";
    string sram_we_path = "tb.dut.sram_we";
    // Are we targeting a read or write operation?
    bit target_write = $urandom_range(0, 1);

    // Disable certain checks for FI.
    cfg.is_fi_test = 1'b1;

    // If we are faulting the sram_we signal, this assertion would trigger. Disable it.
    $assertoff(0, "tb.dut.u_tlul_adapter_sram.u_sram_byte.gen_integ_handling");

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_ops)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_fi_op)

    // Request memory init & enable SRAM readback feature.
    req_mem_init();
    csr_wr(.ptr(ral.readback), .value(MuBi4True));

    // Set the target FI path depending whether we are targeting a write or read.
    if (target_write) begin
      // Either target the adress, the write data, or the write enable signal.
      int idx = $urandom_range(0, 2);
      fi_path = fi_paths[idx];
      fi_mask = fi_masks[idx];
    end else begin
      // Target the read address.
      fi_path = fi_paths[0];
      fi_mask = fi_masks[0];
    end

    // Sanity check some static paths we use in this test.
    `DV_CHECK(uvm_hdl_check_path(fi_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", fi_path))
    `DV_CHECK(uvm_hdl_check_path(sram_req_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", sram_req_path))
    `DV_CHECK(uvm_hdl_check_path(sram_we_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", sram_we_path))

    // As we have at least 10 memory requests, correct the offset.
    fi_iteration_position = do_fi_op - 10;

    // Start the parallel threads.
    fork
      // Driver task.
      drive_reqs(num_ops, target_write);

      // Fault injector task.
      inject_fault(num_ops, fi_iteration_position, fi_path, fi_mask, sram_req_path,
                   sram_we_path, target_write, alert_signal);
    join_any
  endtask : body

endclass : sram_ctrl_readback_err_vseq
