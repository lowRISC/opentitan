// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class chip_sw_lc_ctrl_scrap_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_scrap_vseq)

  `uvm_object_new

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStTestLocked1);


    // Override the test exit token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret0_partition(
        .unlock_token(dec_otp_token_from_lc_csrs(lc_unlock_token)),
        .exit_token(dec_otp_token_from_lc_csrs(lc_exit_token)));
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
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

      // In this test, LC_CTRL will enter the TestLocked state which only allows TAP selection once
      // per boot. Because testbench does not know the exact time when TAP selection happens, we
      // continuously issue LC JTAG read until it returns valid value.
      // In the meantime, TAP selection could happen in between a transaction and might return an
      // error. This error is permitted and can be ignored.
      wait_lc_ready(.allow_err(1));

      jtag_lc_state_transition(DecLcStTestLocked1, DecLcStScrap);

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

      `DV_CHECK_EQ(state, DecLcStScrap)
    end
  endtask : body

  task post_start();
  	// once in SCRAP mode, the CPU can't execute any SW code, so
  	// we don't expect the SW to be done
  	// so we shutdown the device, and then override the test exit from here
  	override_test_status_and_finish(.passed(1));

  	super.post_start();
  endtask : post_start
endclass : chip_sw_lc_ctrl_scrap_vseq
