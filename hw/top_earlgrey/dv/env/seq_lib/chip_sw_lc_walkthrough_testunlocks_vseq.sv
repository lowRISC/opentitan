// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_walkthrough_testunlocks_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_walkthrough_testunlocks_vseq)

  `uvm_object_new

  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit  = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;
  // 7 transitions from TestLockN -> TestUnlockN+1
  localparam uint NumIterations = 7;

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];
  bit [7:0] otp_exit_token[TokenWidthByte];
  bit [7:0] otp_unlock_token[TokenWidthByte];

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset();
    // Wait for `rom_ctrl` to complete the ROM check. This will give the dut
    // enough time to configure the TAP interface before any JTAG agents send
    // any commands.
    wait_rom_check_done();
    set_otp_creator_sw_cfg_rom_exec_en(1);
  endtask

  virtual task body();
    bit [TokenWidthBit-1:0] otp_exit_token_bits, otp_unlock_token_bits;
    dec_lc_state_e curr_state = DecLcStTestLocked0;
    int                    iter = 0;
    super.body();

    otp_exit_token_bits = dec_otp_token_from_lc_csrs(lc_exit_token);
    otp_unlock_token_bits = dec_otp_token_from_lc_csrs(lc_unlock_token);

    otp_unlock_token = {<< 8{otp_unlock_token_bits}};
    otp_exit_token = {<< 8{otp_exit_token_bits}};

    `uvm_info(`gfn, $sformatf("OTP unlock token %0h and OTP exit token %0h",
              otp_unlock_token_bits, otp_exit_token_bits), UVM_LOW)

    // Override the C test tokens with random data.
    sw_symbol_backdoor_overwrite("kOtpExitToken", otp_exit_token);
    sw_symbol_backdoor_overwrite("kOtpUnlockToken", otp_unlock_token);

    wait_lc_ready(.allow_err(1));
    jtag_lc_state_transition(DecLcStRaw, DecLcStTestUnlocked0);
    apply_reset();

    repeat (NumIterations) begin
      `uvm_info(`gfn, $sformatf("iter: %0d / %0d state: %s",
                                iter++, NumIterations, curr_state.name), UVM_MEDIUM)
      `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) ==
            $sformatf("Waiting for LC transtition %0d done and reboot.", curr_state),,
               50_000_000)
      wait_lc_status(LcTransitionSuccessful);
      apply_reset();

      `uvm_info(`gfn, $sformatf("Current state %0s", curr_state.name), UVM_LOW)
      wait_lc_ready(.allow_err(1));
      if (curr_state inside {DecLcStTestLocked0, DecLcStTestLocked1, DecLcStTestLocked2,
                             DecLcStTestLocked3, DecLcStTestLocked4, DecLcStTestLocked5,
                             DecLcStTestLocked6}) begin
        switch_to_external_clock();
      end
      switch_to_external_clock();
      jtag_lc_state_transition(curr_state, dec_lc_state_e'(curr_state + 1), {<<8{lc_unlock_token}});
      apply_reset();
      curr_state = dec_lc_state_e'(curr_state + 2);
    end
  endtask

endclass
