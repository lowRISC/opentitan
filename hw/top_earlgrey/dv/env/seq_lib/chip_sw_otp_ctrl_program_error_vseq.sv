// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_otp_ctrl_program_error_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_otp_ctrl_program_error_vseq)

  `uvm_object_new

  // Reassign `select_jtag` variable to drive LC JTAG tap at start,
  // because LC_CTRL's TestLock state can only sample strap once at boot.
  virtual task pre_start();
    select_jtag = SelectLCJtagTap;
    super.pre_start();
  endtask

  // no need to wait for SW test to complete. As the checks above
  // imply that software has already done its job.
  virtual task wait_for_sw_test_done();
  endtask

  virtual task body();
    logic [lc_ctrl_state_pkg::NumLcCountValues-1:0][lc_ctrl_state_pkg::LcValueWidth-1:0] lc_max_cnt;

    super.body();

    // Backdoor load life cycle transition count to max
    lc_max_cnt = lc_ctrl_state_pkg::LcCnt24;
    for (int i = 0; i < lc_ctrl_state_pkg::NumLcCountValues; i++) begin
      cfg.mem_bkdr_util_h[Otp].write16(otp_ctrl_reg_pkg::LcTransitionCntOffset + i*2,
      lc_max_cnt[i]);
    end

    // Wait for C side to fully stabilize
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Begin life cycle transition");,
             "timeout waiting for C side acknowledgement",
             cfg.sw_test_timeout_ns)

    // poll for state to transition to post transition state
    jtag_csr_spinwait(ral.lc_ctrl.lc_state.get_offset(),
      p_sequencer.jtag_sequencer_h,
      {DecLcStateNumRep{DecLcStPostTrans}},
      cfg.sw_test_timeout_ns);

    // check to ensure that we see a transition count error
    wait_lc_status(LcTransitionCntError);

  endtask


endclass
