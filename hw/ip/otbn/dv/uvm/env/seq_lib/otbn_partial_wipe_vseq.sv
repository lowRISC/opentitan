// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that injects faults to try to trigger bits of a secure wipe, but when they wouldn't
// otherwise be expected. We should expect a fatal error whenever this happens.

class otbn_partial_wipe_vseq extends otbn_single_vseq;
  `uvm_object_utils(otbn_partial_wipe_vseq)
  `uvm_object_new

  // Wait a random time and then force a signal inside the design, which would mean a request for
  // part of a secure wipe, but not in the middle of a real secure wipe.
  task inject_partial_wipe();
    string hdl_path = "tb.dut.u_otbn_core";
    int    ticks_until_err = 1;
    randcase
      1: hdl_path = {hdl_path, ".u_otbn_alu_bignum.sec_wipe_mod_urnd_i"};
      1: hdl_path = {hdl_path, ".u_otbn_controller.sec_wipe_zero_i"};
      1: hdl_path = {hdl_path, ".sec_wipe_base"};
      1: hdl_path = {hdl_path, ".u_otbn_rf_base.sec_wipe_stack_reset_i"};
      1: begin
        hdl_path = {hdl_path, ".sec_wipe_wdr_q"};
        ticks_until_err = 0;
      end
    endcase

    // Wait until we are not doing a secure wipe, and sync up with a negative clock edge (to make
    // the timing more obvious in any trace file)
    `DV_WAIT(cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusySecWipeInt)
    cfg.clk_rst_vif.wait_n_clks(1);

    fork
      begin
        // Force the signal for a cycle, to cause the error
        `uvm_info(`gfn, $sformatf("Injecting error by forcing %0s to 1", hdl_path), UVM_LOW)
        `DV_CHECK_FATAL(uvm_hdl_force(hdl_path, 1) == 1);
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK_FATAL(uvm_hdl_release(hdl_path) == 1);
      end
      begin
        cfg.clk_rst_vif.wait_n_clks(ticks_until_err);
        // Tell the model to jump to the locked state
        cfg.model_agent_cfg.vif.lock_immediately(32'd1 << 20);
      end
    join
  endtask

  task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    // Override the do_end_addr_check flag. It is set in otbn_single_vseq, but we might cause a stop
    // at an unexpected address.
    do_end_addr_check = 1'b0;
  endtask

  task body();
    fork
      super.body();
      inject_partial_wipe();
    join

    // Now wait for the processor to finish: we expect it to lock.
    `DV_WAIT(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked)
    reset_if_locked();
  endtask

endclass
