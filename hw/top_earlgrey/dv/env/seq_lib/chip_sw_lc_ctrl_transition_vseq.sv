// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_lc_ctrl_transition_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_transition_vseq)

  `uvm_object_new

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  // Reassign `select_jtag` variable to drive LC JTAG tap at start,
  // because LC_CTRL's TestLock state can only sample strap once at boot.
  virtual task pre_start();
    select_jtag = SelectLCJtagTap;
    super.pre_start();
  endtask

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStTestLocked1);

    // Override the test exit token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret0_partition(
        .unlock_token(get_otp_token(lc_unlock_token)),
        .exit_token(get_otp_token(lc_exit_token)));
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    backdoor_override_otp();
  endtask

  // This function takes the token value from LC_CTRL token CSRs, then runs through cshake128 to
  // get a 768-bit XORed token output.
  // The first 128 bits of the decoded token should match the OTP's secret0 paritition's
  // descrambled tokens value.
  virtual function bit [TokenWidthBit-1:0] get_otp_token(
      bit [7:0] token_in[TokenWidthByte]);

    bit [7:0]                      dpi_digest[kmac_pkg::AppDigestW/8];
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;

    digestpp_dpi_pkg::c_dpi_cshake128(token_in, "", "LC_CTRL", TokenWidthByte,
                                      kmac_pkg::AppDigestW/8, dpi_digest);

    digest_bits = {<< byte {dpi_digest}};
    return (digest_bits[TokenWidthBit-1:0]);
  endfunction

  virtual task body();
    super.body();

    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      // sw_symbol_backdoor_overwrite takes an array as the input.
      bit [7:0] trans_i_array[] = {trans_i};
      sw_symbol_backdoor_overwrite("kTestIterationCount", trans_i_array);

      if (trans_i > 1) begin
        apply_reset();
        backdoor_override_otp();
      end

      // Override the C test kLcExitToken with random data.
      sw_symbol_backdoor_overwrite("kLcExitToken", lc_exit_token);

      // In this test, LC_CTRL will enter the TestLocked state which only allows TAP selection once
      // per boot. Because testbench does not know the exact time when TAP selection happens, we
      // continuously issue LC JTAG read until it returns valid value.
      // In the meantime, TAP selection could happen in between a transaction and might return an
      // error. This error is permitted and can be ignored.
      wait_lc_ready(.allow_err(1));

      jtag_lc_state_transition(DecLcStTestLocked1, DecLcStTestUnlocked2, {<<8{lc_unlock_token}});

      // LC state transition requires a chip reset.
      apply_reset();

      // Wait for SW to finish power on set up.
      wait (cfg.sw_logger_vif.printed_log == "Start LC_CTRL transition test.");

      // Wait for LC_CTRL state trasition finish from TLUL interface.
      wait_lc_status(LcTransitionSuccessful);

      // LC_CTRL state transition requires a chip reset.
      apply_reset();

      // Wait for SW test finishes with a pass/fail status.
      wait (cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusPassed,
                                                          SwTestStatusFailed});
      `uvm_info(`gfn, $sformatf("Sequence %0d/%0d finished!", trans_i, num_trans), UVM_LOW)
    end
  endtask

endclass
