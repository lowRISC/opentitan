// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_ctrl_program_error_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_program_error_vseq)

  `uvm_object_new

  // Reassign `select_jtag` variable to drive LC JTAG tap at start,
  // because LC_CTRL's TestLock state can only sample strap once at boot.
  virtual task pre_start();
    select_jtag = SelectLCJtagTap;
    super.pre_start();
  endtask

  virtual task body();
    bit [TL_DW-1:0] status_val;
    string otp_path = {`DV_STRINGIFY(`OTP_CTRL_HIER),
                       ".u_otp_ctrl_lci.lc_err_o"};

    super.body();

    // Wait for C side to fully stabilize
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Begin life cycle transition");,
             "timeout waiting for C side acknowledgement",
             cfg.sw_test_timeout_ns)

    // force lc_ctrl program path to error
    `DV_CHECK_FATAL(uvm_hdl_force(otp_path, 1'b1));

    // poll for state to transition to post transition state
    jtag_csr_spinwait(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      {DecLcStateNumRep{DecLcStEscalate}},
      cfg.sw_test_timeout_ns);

    `uvm_info(`gfn, $sformatf("post trans observed"), UVM_LOW)

    // check to ensure that we see an otp error
    jtag_read_csr(ral.lc_ctrl.status.get_offset(),
      p_sequencer.jtag_sequencer_h,
      status_val);

    `DV_CHECK_FATAL(status_val & (1 << LcOtpError));
  endtask
endclass
