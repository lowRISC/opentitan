// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class chip_sw_lc_ctrl_raw_to_scrap_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_raw_to_scrap_vseq)

  `uvm_object_new

  protected bit _end_of_test = 1'b0;

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStRaw);
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    // setting 'expect_fatal_alert' = 1 will trigger a dut_init at the end of the test
    // which will change the SW logger from pass/fail to reset, which will result in a uvm error
    // when entering the cleanup phases of the sequence
    // so if we're at the end of the sequence, don't perform dut_init
    if (_end_of_test) begin
      return;
    end

    super.dut_init(reset_kind);
    backdoor_override_otp();
  endtask

  virtual task body();
    super.body();

    `uvm_info(`gfn, $sformatf("Will run for %d iterations", num_trans), UVM_MEDIUM)
    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      // sw_symbol_backdoor_overwrite takes an array as the input.
      bit [7:0] trans_i_array[] = {trans_i};
      bit [TL_DW-1:0] ext_clock_en;
      bit [BUS_DW-1:0] state;

      if (trans_i > 1) begin
        `uvm_info(`gfn, $sformatf("Applying reset and otp override for trans %d", trans_i),
                  UVM_MEDIUM)
        apply_reset();
        backdoor_override_otp();
      end

      wait_lc_ready(.allow_err(1));

      jtag_lc_state_transition(DecLcStRaw, DecLcStScrap);

      // LC state transition requires a chip reset.
      `uvm_info(`gfn, $sformatf("Applying reset after lc transition for trans %d", trans_i),
                UVM_MEDIUM)
      apply_reset();

      // acquire access for JTAG to LC CTRL
       wait_lc_initialized(.allow_err(1));

      // check LC state is indeed in SCRAP
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                          p_sequencer.jtag_sequencer_h,
                                          state);

      `DV_CHECK_EQ(state, {6{DecLcStScrap}})
    end
  endtask : body

  task post_start();
  	// once in SCRAP mode, the CPU can't execute any SW code, so
  	// we don't expect the SW to be done
  	// so we shutdown the device, and then override the test exit from here
    override_test_status_and_finish(.passed(1));

    // changing into SCRAP mode fires an alert from OTP controller
    // but as we expect this, don't check for fatal alerts
    expect_fatal_alerts = 1'b1;

    // cip_base_vseq::post_start calls `dut_init` when expect_fatal_alerts == 1
    //
    // this will change the SW logger status from pass/failed to reset, and will
    // cause false `uvm_error when checking on the logger status
    // when the vseq is in its closing stage
    //
    // _end_of_test == 1 will prevent this.dut_init from actually performing a reset
    // and thus will bypass the problem
    _end_of_test = 1'b1;

    super.post_start();
  endtask : post_start
endclass : chip_sw_lc_ctrl_raw_to_scrap_vseq
