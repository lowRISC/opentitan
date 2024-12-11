// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// mubi_enc_err_vseq
class sram_ctrl_mubi_enc_err_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_mubi_enc_err_vseq)

  `uvm_object_new

  // Indicates the number of memory accesses to be performed in this test.
  rand int num_ops;

  // Indicates at which memory access the fault is injected.
  rand int fi_op_idx;

  constraint num_ops_c {
    num_ops inside {[10 : 200]};
  }

  constraint fi_op_idx_c {
    fi_op_idx inside {[1 : num_ops - 1]};
  }

  int fi_iteration_position = 0;

  task wait_for_signal(string path);
    // Wait until the signal is 1.
    bit req = 1'b0;
    `DV_SPINWAIT(
      do begin
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK_FATAL(uvm_hdl_read(path, req));
      end while(!req);
    )
  endtask

  task drive_reqs(int iterations, bit write);
    // Perform random read/write operations.
    bit [TL_AW-1:0] sram_addr_mask = cfg.ral_models[cfg.sram_ral_name].get_addr_mask();
    bit [TL_AW-1:0] max_offset = {sram_addr_mask[TL_AW-1:2], 2'd0};
    logic [TL_DW-1:0] rdata;
    for (int iteration = 0; iteration < iterations; iteration++) begin
        bit [TL_AW-1:0] addr;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr, (addr & sram_addr_mask) < max_offset;)
        if (write) begin
          do_single_write(.addr(addr), .data(iteration), .mask('1), .blocking(0));
        end else begin
          do_single_read(.addr(addr), .mask('1), .check_rdata(0), .blocking(0), .rdata(rdata));
        end
    end
  endtask

  task inject_fault(int iterations, int iteration_fi_position, string fi_path,
                    string sram_req_path, string sram_we_path, bit write_op,
                    string alert_signal);
    // Inject a fault into the signal indicated by fi_path & monitor the response.
    int value;
    int value_faulty;
    int fault_bit_pos;
    // Sanity check fault position is within the number of iterations.
    `DV_CHECK_LT_FATAL(iteration_fi_position, iterations)
    for (int iteration = 0; iteration < iteration_fi_position; iteration++) begin
      // Wait until the sram_we (for writes) or the sram_req (for reads) arrives.
      if (write_op) begin
        wait_for_signal(sram_we_path);
      end else begin
        wait_for_signal(sram_req_path);
      end
    end

    // We have reached the transaction we were waiting for, start injecting
    // the fault.
    `uvm_info(`gfn, $sformatf(
              "Injecting fault into %s in memory operation %d and check the %s alert",
              fi_path, iteration_fi_position, alert_signal),
              UVM_LOW)
    // Configure which alert we are expecting.
    cfg.scb.set_exp_alert(alert_signal, .is_fatal(1'b1), .max_delay(20));
    fork
      begin : inject_fault
        `DV_CHECK_FATAL(uvm_hdl_read(fi_path, value));
        fault_bit_pos = $urandom_range(1, 4);
        value_faulty = value ^ fault_bit_pos;
        `DV_CHECK_FATAL(uvm_hdl_force(fi_path, value_faulty))
        // Release the faulty signal after one clock cycle.
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK_FATAL(uvm_hdl_release(fi_path))
      end : inject_fault
      begin : monitor_response
        // Check if alert_signal was triggered.
        wait_alert_trigger (alert_signal, .max_wait_cycle(20), .wait_complete(0));
      end : monitor_response
    join
    // Reset to get the DUT out of terminal state.
    apply_resets_concurrently();
  endtask

  task body();
    // Define the signal we are targeting to inject a fault. This list covers
    // critical signals within the prim_ram macro that are multi-bit encoded
    // and should trigger an alert when detecting an invalid encoding.
    string fi_paths[8] = {"tb.dut.u_prim_ram_1p_scr.write_en_q",
                          "tb.dut.u_prim_ram_1p_scr.addr_collision_q",
                          "tb.dut.u_prim_ram_1p_scr.write_pending_q",
                          "tb.dut.u_prim_ram_1p_scr.rvalid_q",
                          "tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.req_q",
                          "tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.write_q",
                          "tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.rvalid_q",
                          "tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.rvalid_sram_q"};
    // These variables hold the randomly selected target signal.
    string fi_path;
    // Used to keep track of the incoming TL-UL requests.
    string sram_req_path = "tb.dut.sram_req";
    string sram_we_path = "tb.dut.sram_we";
    // The multi-bit encoding raises the fatal_error alert on a mismatch.
    string alert_signal = "fatal_error";
    // Are we targeting a read or write operation?
    bit target_write = $urandom_range(0, 1);

    // Disable certain checks for FI.
    cfg.is_fi_test = 1'b1;

    // Turn off tlul_adapter_sram assertions as we are messing around with some
    // signals that would trigger an assertion.
    $assertoff(0, "tb.dut.u_tlul_adapter_sram");
    // As we injecting faults into prim_ram, disable TL-UL integrity checks.
    cfg.m_tl_agent_cfgs[cfg.sram_ral_name].check_tl_errs = 0;

    // Request memory init.
    req_mem_init();

    // Set the target FI path randomly.
    fi_path = fi_paths[$urandom_range(0, 7)];

    // Start the parallel threads.
    fork
      // Driver task.
      drive_reqs(num_ops, target_write);

      // Fault injector task.
      inject_fault(num_ops, fi_op_idx, fi_path, sram_req_path,
                   sram_we_path, target_write, alert_signal);
    join
  endtask : body

endclass : sram_ctrl_mubi_enc_err_vseq
