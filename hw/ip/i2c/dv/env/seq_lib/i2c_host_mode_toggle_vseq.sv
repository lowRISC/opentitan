// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// In DUT=host_mode, create a read/write transaction and randomly disable host_mode
//   mid-transaction by writing ctrl.enablehost = 1'b0.
// Check if DUT goes to Idle state
// To check the DUT has recovered, start a host_smoke_vseq to check transactions
//   are processed as expected
class i2c_host_mode_toggle_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_host_mode_toggle_vseq)
  `uvm_object_new

  rand bit rwbit;
  rand bit[6:0] addr;
  uint num_bytes = 1;
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
    expected_intr[AcqFull] = 1;
    expected_intr[TxStretch] = 1;
    expected_intr[CmdComplete] = 1;
    // Since after driver reset, SDA will be high, NAK interrupt will be raised
    expected_intr[ControllerHalt] = 1;
    expected_intr[HostTimeout] = 1;
    for (int i = 0; i < NumI2cIntr; i++) intr_q.push_back(i2c_intr_e'(i));
    if (cfg.bad_addr_pct > 0) cfg.m_i2c_agent_cfg.allow_bad_addr = 1;
  endtask

  virtual task body();
    i2c_item fmt_item = new("addr_item");
    bit [TL_DW-1:0] reg_val;
    initialization();
    get_timing_values();
    program_registers();
    `uvm_info(`gfn, "Start i2c_host_mode_toggle_vseq", UVM_HIGH)
    // start transmission in Host mode with a random read or write transaction
    fmt_item.start = 1;
    fmt_item.read = rwbit;
    fmt_item.fbyte = {addr, rwbit};
    program_format_flag(fmt_item, "Programming address in host mode", 1);
    fmt_item = new("data_item");
    if (rw_bit) begin // if read enable one byte read
      fmt_item.read = 1;
      fmt_item.fbyte = num_bytes;
    end
    else begin // if write send one byte
      fmt_item.fbyte = $urandom_range(0,255);
    end
    fmt_item.stop = 1;
    program_format_flag(fmt_item, "Programming data in host mode", 1);
    // Wait for random number of cycles
    repeat (wait_cycles) @(posedge cfg.m_i2c_agent_cfg.vif.scl_io);
    `uvm_info(`gfn, "Disabling host mode", UVM_LOW)
    // Disable host mode
    cfg.en_scb = 0;
    ral.ctrl.enablehost.set(1'b0);
    csr_update(ral.ctrl);
    // Clear Host mode FIFO
    ral.fifo_ctrl.rxrst.set(1'b1);
    ral.fifo_ctrl.fmtrst.set(1'b1);
    csr_update(ral.fifo_ctrl);
    // Wait for DUT to be in idle mode
    do begin
      csr_rd(.ptr(ral.status), .value(reg_val));
      cfg.clk_rst_vif.wait_clks(1);
    end while(!bit'(get_field_val(ral.status.hostidle, reg_val)));
    `uvm_info(`gfn, "DUT in idle mode", UVM_LOW)
    // Clear all interrupts
    process_interrupts();
    // Clear scoreboard FIFO
    cfg.scb_h.target_mode_wr_exp_fifo.flush();
    cfg.scb_h.target_mode_wr_obs_fifo.flush();
    // Enable scorebaord
    cfg.en_scb = 1;
    `uvm_info(`gfn, "Enable Host mode", UVM_LOW)
    cfg.m_i2c_agent_cfg.if_mode = Device;
    // Enable host mode
    ral.ctrl.enablehost.set(1'b1);
    csr_update(ral.ctrl);
    cfg.clk_rst_vif.wait_clks(10);
    // Start host_smoke
    begin
      uvm_sequence seq = create_seq_by_name("i2c_host_smoke_vseq");
      seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(seq)
      seq.start(p_sequencer);
    end
    `uvm_info(`gfn, "End i2c_host_mode_toggle_vseq", UVM_HIGH)
  endtask : body


endclass
