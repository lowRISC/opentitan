// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_ctrl_program_error_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_program_error_vseq)

  `uvm_object_new

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual task body();
    bit [TL_DW-1:0] status_val;

    super.body();

    // Wait for C side to fully stabilize
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Begin life cycle transition");,
             "timeout waiting for C side acknowledgement",
             cfg.sw_test_timeout_ns)

    // force lc_ctrl program path to error
    void'(cfg.chip_vif.signal_probe_otp_ctrl_lc_err_o(SignalProbeForce, 1));

    // poll for state to transition to post transition state
    jtag_csr_spinwait(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      {DecLcStateNumRep{DecLcStEscalate}},
      cfg.sw_test_timeout_ns);

    `uvm_info(`gfn, $sformatf("post trans observed"), UVM_LOW)

    // This is used for toggle coverage collection purpose to cover the `lc_err_o` transition from
    // 1 to 0.
    void'(cfg.chip_vif.signal_probe_otp_ctrl_lc_err_o(SignalProbeRelease));

    // check to ensure that we see an otp error
    jtag_read_csr(ral.lc_ctrl.status.get_offset(),
      p_sequencer.jtag_sequencer_h,
      status_val);

    `DV_CHECK_FATAL(status_val & (1 << LcOtpError));

  endtask
endclass
