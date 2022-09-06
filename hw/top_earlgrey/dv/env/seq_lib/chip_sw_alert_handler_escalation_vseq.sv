// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_escalation_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_alert_handler_escalation_vseq)

  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(SelectLCJtagTap);
    super.pre_start();
  endtask

  virtual task body();
    string keymgr_path = {`DV_STRINGIFY(tb.dut.`KEYMGR_HIER),
                        ".u_ctrl.key_state_q"};
    logic [1023:0] curr_key, prev_key;
    logic [TL_DW-1:0] init_state;
    logic [TL_DW-1:0] reg_val;
    bit [LcBroadcastLast-1:0] bool_vector;

    super.body();

    // ensure we see NMI handler trigger from C side
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Keymgr entered Init State");,
             "timeout waiting for C side keymgr init acknowledgement",
             cfg.sw_test_timeout_ns)

    if (!uvm_hdl_read(keymgr_path, curr_key)) begin
       `uvm_fatal(`gfn, $sformatf("uvm_hdl_read failed for %0s", keymgr_path))
    end

    // Read current lc state to establish baseline
    jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      init_state
    );
    `uvm_info(`gfn, $sformatf("Initial state is 0x%h", init_state), UVM_LOW)

    // ensure we see NMI handler trigger from C side
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "You are experiencing an NMI");,
             "timeout waiting for C side NMI acknowledgement",
             cfg.sw_test_timeout_ns)

    // Read lc state to ensure that we are still in normal operating mode
    jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      reg_val
    );

    if (reg_val != init_state) begin
      `uvm_fatal(`gfn, $sformatf("Unexpected LC state change from 0x%h to 0x%h",
                 init_state, reg_val))
    end else begin
    `uvm_info(`gfn, $sformatf("Initial state is 0x%h, current state is 0x%h", init_state, reg_val),
              UVM_LOW)
    end

    // poll for state to transition into escalate
    jtag_csr_spinwait(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      {DecLcStateNumRep{DecLcStEscalate}},
      cfg.sw_test_timeout_ns);

    prev_key = curr_key;
    `DV_CHECK_FATAL(uvm_hdl_read(keymgr_path, curr_key))
    if (curr_key == prev_key) begin
      `uvm_fatal(`gfn, $sformatf("something is very wrong"))
    end

    // once in scrap, probe and check for broadcasts
    bool_vector = '0;
    bool_vector[EscEn] = 1;
    check_lc_ctrl_broadcast(bool_vector);
  endtask

endclass
