// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence requires to define following variable in c test.
// static volatile const uint8_t kExternalClockEnable;
// Default is 0.
// If this variable is set to 1, c test takes lc_ctrl_mutex and
// do lc state transition.
class chip_sw_lc_ctrl_transition_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_transition_vseq)

  `uvm_object_new

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];

  constraint num_trans_c {num_trans inside {[1 : 2]};}

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
    bit [7:0] ext_clock_en_array[1];
    super.body();
    `uvm_info(`gfn, $sformatf("Will run for %0d iterations", num_trans), UVM_MEDIUM)
    sw_symbol_backdoor_read("kExternalClockEnable", ext_clock_en_array);
    for (int trans_i = 1; trans_i <= num_trans; trans_i++) begin
      // sw_symbol_backdoor accesses take arrays as the input and output.
      bit [7:0] trans_i_array[] = {trans_i};
      bit [TL_DW-1:0] ext_clock_en;

      sw_symbol_backdoor_overwrite("kTestIterationCount", trans_i_array);

      if (trans_i > 1) begin
        `uvm_info(`gfn, $sformatf("Applying reset and otp override for trans %0d", trans_i),
                  UVM_MEDIUM)
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

      // This is for a temporary tb patch.
      // Before using jtag, wait for lc_ctrl is ready.
      wait_rom_check_done();
      wait_lc_ready(.allow_err(1));

      fork
        begin : isolation_fork_lc
          bit external_clock_was_activated = 1'b0;

          // Detect windows when the AST selects ext_clk to drive the io_clk, to verify the external
          // clock, and not the io oscillator, is actually used for these lc_ctrl transitions.
          fork
            begin
              `uvm_info(`gfn, "Start detection of ext_clk active window", UVM_MEDIUM)
              cfg.ast_ext_clk_vif.span_external_clock_active_window();
              external_clock_was_activated = 1'b1;
            end
          join_none

          // TEST_LOCKED* LC states do not allow ROM code execution -> IO clock calibration values
          // aren't copied from OTP to AST -> internal clock isn't calibrated -> use external clock
          // to perform LC transition

          // activate the external source clock with 48MHz
          switch_to_external_clock();

          // Check external clock is switched.
          csr_spinwait(.ptr(ral.lc_ctrl.status.ext_clock_switched), .exp_data(1'b1),
                       .backdoor(1), .timeout_ns(100_000));
          `DV_CHECK(cfg.ast_ext_clk_vif.is_ext_clk_in_use(),
                    "external clock should be ready before state transition");

          // perform the first LC state transition using LC JTAG
          `uvm_info(`gfn, "Performing state transition", UVM_MEDIUM)
          jtag_lc_state_transition(DecLcStTestLocked1, DecLcStTestUnlocked2,
                                   {<<8{lc_unlock_token}});

          // JTAG read out if LC_CTRL is configured to use external clock.
          jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.transition_ctrl.get_offset(),
                                              p_sequencer.jtag_sequencer_h, ext_clock_en);
          `DV_CHECK(ext_clock_en,
                    "jtag read lc_ctrl.transition_ctrl should be 1");

          // LC state transition requires a chip reset.
          `uvm_info(`gfn, $sformatf("Applying reset after lc transition for trans %0d", trans_i),
                    UVM_MEDIUM)
          apply_reset();

          `DV_CHECK(external_clock_was_activated, "External clock should be enabled");

          disable fork;
        end : isolation_fork_lc
      join

      // At this point the LC_CTRL state should be TEST_UNLOCKED2.
      // Wait for SW to finish power on set up.
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Waiting for LC transition done and reboot.")

      fork
        begin : isolation_fork_sw
          bit external_clock_was_activated = 1'b0;

          // Detect windows when the AST selects ext_clk to drive the io_clk, to verify the external
          // clock, and not the io oscillator, is actually used for these lc_ctrl transitions.
          fork
            begin
              `uvm_info(`gfn, "Start detection of ext_clk active window", UVM_MEDIUM)
              cfg.ast_ext_clk_vif.span_external_clock_active_window();
              external_clock_was_activated = 1'b1;
            end
          join_none

          // Get the interface back to jtag.
          claim_transition_interface();

          // Wait for LC_CTRL state transition finish from TLUL interface.
          wait_lc_status(LcTransitionSuccessful);

          // JTAG read out if LC_CTRL is configured to use external clock.
          jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.transition_ctrl.get_offset(),
                                              p_sequencer.jtag_sequencer_h, ext_clock_en);
          // Check external clock is as expected by software.
          `DV_CHECK(ext_clock_en == ext_clock_en_array[0]);

          // LC_CTRL state transition requires a chip reset.
          apply_reset();
          `uvm_info(`gfn, "Second apply_reset done", UVM_MEDIUM)

          `DV_CHECK(external_clock_was_activated == ext_clock_en, $sformatf(
                    "Expected external clock %0s activated", ext_clock_en ? "was" : "wasn't"));
          disable fork;
        end : isolation_fork_sw
      join

      // Wait for SW test finishes with a pass/fail status.
      `DV_WAIT(
          cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusPassed, SwTestStatusFailed})
      `uvm_info(`gfn, $sformatf("Sequence %0d/%0d finished!", trans_i, num_trans), UVM_LOW)
    end
  endtask

endclass
