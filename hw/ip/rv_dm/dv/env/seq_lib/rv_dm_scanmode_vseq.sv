// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A vseq that enables scanmode and sends a very simple JTAG transaction.
//
// This doesn't use the normal JTAG driver, because that driver expects to be able to *drive* TCK.
// This doesn't really work in scanmode, where TCK is the main clk_i input.
class rv_dm_scanmode_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_scanmode_vseq)
  `uvm_object_new

  // Override the base class constraint that would normally disable scanmode. We want to enable it.
  constraint no_scanmode_c {
    scanmode == 1'b1;
  }

  // Set tms/tdi as requested and then wait for the next negedge of clk (which gets to the
  // corresponding negedge of TCK because we are in scanmode).
  task tms_tdi(bit tms, bit tdi);
    cfg.m_jtag_agent_cfg.vif.tms = tms;
    cfg.m_jtag_agent_cfg.vif.tdi = tdi;
    cfg.clk_rst_vif.wait_n_clks(1);
  endtask

  // Set tms as requested and drive a tdi of zero (which hopefully won't matter)
  task send_tms(bit tms);
    tms_tdi(tms, 0);
  endtask

  // Send value over IR or DR. td_o is collected and appears in the dout output argument.
  //
  // This task assumes we start in Select-*R-Scan, then completes back in Run-Test/Idle
  task select_to_update(int unsigned value, int unsigned len, output logic [JTAG_DRW-1:0] dout);
    `DV_CHECK_FATAL((value >> len) == 0)
    `DV_CHECK_FATAL(len != 0)

    send_tms(1'b0); // Capture-*R
    send_tms(1'b0); // Shift-*R

    dout = '0;

    for (int i = 0; i < len; i++) begin
      dout[i] = cfg.m_jtag_agent_cfg.vif.tdo;
      tms_tdi(i == len - 1, value[i]);
    end

    send_tms(1'b1); // Update-*R
    send_tms(1'b0); // Run-Test/Idle
  endtask

  // Send an IR or DR transaction with the given value.
  //
  // The task assumes that we start in Run-Test/Idle, then completes in the same state. Exits
  // immediately on a system reset.
  task send_xr(bit is_ir, int unsigned value, int unsigned len, output logic [JTAG_DRW-1:0] dout);
    fork begin : isolation_fork
      fork
        begin
          send_tms(1'b1);            // Select-DR-Scan
          if (is_ir) send_tms(1'b1); // Select-IR-Scan
          select_to_update(value, len, dout);
        end
        wait(!cfg.clk_rst_vif.rst_n);
      join_any
      disable fork;
    end join
  endtask

  // Send an IR transaction with the given value.
  //
  // The task assumes that we start in Run-Test/Idle, then completes in the same state. Exits
  // immediately on a system reset.
  task send_ir(int unsigned value, int unsigned len);
    logic [JTAG_DRW-1:0] dout;
    send_xr(1'b1, value, len, dout);
  endtask

  // Send a DR transaction with the given value, sending td_o back in the dout argument.
  //
  // The task assumes that we start in Run-Test/Idle, then completes in the same state. Exits
  // immediately on a system reset.
  task send_dr(int unsigned value, int unsigned len, output logic [JTAG_DRW-1:0] dout);
    send_xr(1'b0, value, len, dout);
  endtask

  task body();
    logic [JTAG_DRW-1:0] data, dout;
    int unsigned         len;

    data = $urandom_range(0, 16'hffff);
    len = 16;

    // Wait for trst_n to go high, which should ensure that the JTAG connection has been made
    // properly.
    wait(cfg.m_jtag_agent_cfg.mon_vif.trst_n);

    // Start by making sure the TAP fsm is in the Test-Logic/Reset state, then go to Run-Test/Idle.
    // Exit early if there is a system reset.
    fork begin : isolation_fork
      fork
        begin
          repeat (5) tms_tdi(1'b1, 1'b0);
          send_tms(0); // Go to Run-Test/Idle
        end
        wait(!cfg.clk_rst_vif.rst_n);
      join_any
      disable fork;
    end join
    if (!cfg.clk_rst_vif.rst_n) return;

    // Select the BYPASS register (which has an IR of 0, different from the reset value, IDCODE).
    // Exit immediately if we get to system reset.
    `uvm_info(`gfn, "Selecting BYPASS register", UVM_LOW)
    send_ir(8'h0, 8);
    if (!cfg.clk_rst_vif.rst_n) return;

    // Now write an arbitrary value and read it back out (shifted). Then exit if we get to system
    // reset.
    `uvm_info(`gfn, $sformatf("Writing arbitrary value (%0h) to BYPASS register", data), UVM_LOW)
    send_dr(data, len, dout);
    if (!cfg.clk_rst_vif.rst_n) return;

    // The value that we read back out should equal the one we started with, with two zeros inserted
    // at the bottom positions.
    `DV_CHECK_EQ(dout, (data << 2) & 16'hffff)
  endtask
endclass
