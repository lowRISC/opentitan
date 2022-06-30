// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_escalation_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_alert_handler_escalation_vseq)

  `uvm_object_new

  lc_ctrl_state_pkg::dec_lc_state_e state_val = lc_ctrl_state_pkg::DecLcStRaw;

  // Reassign `select_jtag` variable to drive LC JTAG tap at start,
  // because LC_CTRL's TestLock state can only sample strap once at boot.
  virtual task pre_start();
    select_jtag = SelectLCJtagTap;
    super.pre_start();
  endtask

  virtual task body();
    string keymgr_path = {`DV_STRINGIFY(`KEYMGR_HIER),
                        ".u_ctrl.key_state_q"};
    logic [1023:0] curr_key, prev_key;
    super.body();

    // ensure we see NMI handler trigger from C side
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Keymgr entered Init State");,
             "timeout waiting for C side keymgr init acknowledgement",
             cfg.sw_test_timeout_ns)

    if (!uvm_hdl_read(keymgr_path, curr_key)) begin
       `uvm_fatal(`gfn, $sformatf("uvm_hdl_read failed for %0s", keymgr_path))
    end


    // ensure we see NMI handler trigger from C side
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "You are experiencing an NMI");,
             "timeout waiting for C side NMI acknowledgement",
             cfg.sw_test_timeout_ns)

    // poll for state to transition into scrap
    jtag_csr_spinwait(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      {DecLcStateNumRep{DecLcStEscalate}},
      cfg.sw_test_timeout_ns);

    prev_key = curr_key;
    uvm_hdl_read(keymgr_path, curr_key);
    if (curr_key == prev_key) begin
      `uvm_fatal(`gfn, $sformatf("something is very wrong"))
    end


  endtask

endclass
