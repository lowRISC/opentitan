// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq stimulates a mid-transfer deactivation of the DUT's Controller-Mode module
// by writing ctrl.enablehost = 1'b0 at a random point during an active I2C Transaction.
// - Configure the DUT, and drive a normal controller-mode transfer.
// - Randomly disable Host-Mode mid transfer.
// - Wait for the DUT to go back to the Idle state.
// - Re-activate the controller-mode module, and drive a new transaction to test recovery.
//
class i2c_host_mode_toggle_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_host_mode_toggle_vseq)
  `uvm_object_new

  rand bit rwbit;
  rand bit[6:0] addr;
  rand uint wait_cycles;
  // Wait for address byte or data byte with equal probability
  constraint wait_cycles_c{
    wait_cycles dist {
        [1:7] := 1,
        [9:17] := 1
    };
  }


  virtual task pre_start();
    super.pre_start();

    // Mark the interrupts we expect to assert during this test. If any other interrupts assert,
    // immediately raise a fatal error.
    expected_intr[AcqStretch] = 1;
    expected_intr[TxStretch] = 1;
    expected_intr[CmdComplete] = 1;
    expected_intr[ControllerHalt] = 1;
    expected_intr[HostTimeout] = 1;
    for (int i = 0; i < NumI2cIntr; i++) intr_q.push_back(i2c_intr_e'(i));
  endtask


  virtual task body();

    initialization();
    get_timing_values();
    program_registers();

    `uvm_info(`gfn, "Start i2c_host_mode_toggle_vseq", UVM_HIGH)

    // Drive a new DUT-Controller transfer, which may be either a 1-byte read or write

    // The first write initiates the transaction via the start condition, then the addr+dir byte
    begin
      i2c_item fmt_item = new("fmt_item");
      fmt_item.start = 1;
      fmt_item.fbyte = {addr, rw_bit};
      program_format_flag(fmt_item, "Programming address in host mode");
    end
    // The second write determines tx or rx for the one data byte, then drives a STOP condition.
    begin
      i2c_item fmt_item = new("fmt_item");
      if (rw_bit == i2c_pkg::READ) begin
        fmt_item.read = 1;
        fmt_item.fbyte = 1; // Just do a one byte read transfer
      end
      else begin // Do a one byte write transfer
        fmt_item.fbyte = $urandom;
      end
      fmt_item.stop = 1;
      program_format_flag(fmt_item, "Programming data in host mode");
    end

    // Before disabling the CONTROLLER module via ctrl.enablehost, wait for random number of
    // SCL cycles to ensure we are mid-transfer on the bus.
    repeat (wait_cycles) @(posedge cfg.m_i2c_agent_cfg.vif.scl_io);

    // Disable scoreboard
    cfg.en_scb = 0;
    begin

      // Disable the host mode module now.
      `uvm_info(`gfn, "Disabling host mode now.", UVM_LOW)
      ral.ctrl.enablehost.set(1'b0);
      csr_update(ral.ctrl);

      // Wait for DUT to return to idle.
      csr_spinwait(ral.status.hostidle, 1'b1,
        .spinwait_delay_ns(( cfg.clk_rst_vif.clk_period_ps / 1000 ) * 10 /* 10 clk_i cycles*/),
        .timeout_ns(10_000));

      `uvm_info(`gfn, "DUT has returned to idle now.", UVM_LOW)

      // Clear out any remaining state in the Controller-Mode FIFOs.
      ral.fifo_ctrl.rxrst.set(1'b1);
      ral.fifo_ctrl.fmtrst.set(1'b1);
      csr_update(ral.fifo_ctrl);

      // Clear any pending Controller-Mode interrupts
      process_interrupts();

      // Clear scoreboard FIFO
      cfg.scoreboard.target_mode_wr_exp_fifo.flush();
      cfg.scoreboard.target_mode_wr_obs_fifo.flush();

    end
    // Re-enable scorebaord
    cfg.en_scb = 1;

    // Re-enable host mode
    `uvm_info(`gfn, "Re-enabling the Controller-Module now.", UVM_LOW)
    ral.ctrl.enablehost.set(1'b1);
    csr_update(ral.ctrl);

    // Start a DUT-Controller stimulus transaction to test recovery
    // - Limit the size of the transfer just to keep this test fast, as we get no additional
    //   coverage from extra data in the smoke sequence.
    cfg.clk_rst_vif.wait_clks(10);
    begin
      i2c_host_smoke_vseq seq;
      `uvm_create_obj(i2c_host_smoke_vseq, seq)
      seq.set_sequencer(p_sequencer);
      seq.num_trans_c.constraint_mode(0);
      seq.num_runs_c.constraint_mode(0);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(seq,
        num_trans == 3;
        num_runs == 3;
        num_wr_bytes == 15;
        num_rd_bytes == 15;)
      seq.start(p_sequencer);
    end
    `uvm_info(`gfn, "End i2c_host_mode_toggle_vseq", UVM_HIGH)
  endtask : body


endclass
