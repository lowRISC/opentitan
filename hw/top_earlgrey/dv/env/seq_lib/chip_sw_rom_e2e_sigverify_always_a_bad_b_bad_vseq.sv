// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq extends
  chip_sw_rom_e2e_shutdown_output_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq)
  `uvm_object_new

  lc_ctrl_state_pkg::lc_state_e lc_state;

  // Matches BFV.SIGVERIFY.BAD_ENCODED_MSG in `rules/const.bzl`.
  string bfv = "01535603";

  // This matches the expected values in `sw/device/silicon_creator/rom/e2e/BUILD`. Note,
  // SystemVerilog does not support "\r" carriage return in a string literal, so we use the hex code
  // of "\x0d" instead. Also note, this cannot be a localparam as it turns out, our SV compiler
  // does not seem to have any knowledge of `lc_state_e` enum at the time when it is processing
  // localparams.
  string exp_boot_fault_msgs[lc_ctrl_state_pkg::lc_state_e] = '{
      lc_ctrl_state_pkg::LcStTestUnlocked0: $sformatf("BFV:%0s\x0d\nLCV:02108421\x0d\n", bfv),
      lc_ctrl_state_pkg::LcStDev:           $sformatf("BFV:%0s\x0d\nLCV:21084210\x0d\n", bfv),
      lc_ctrl_state_pkg::LcStProd:          $sformatf("BFV:%0s\x0d\nLCV:2318c631\x0d\n", bfv),
      lc_ctrl_state_pkg::LcStProdEnd:       $sformatf("BFV:%0s\x0d\nLCV:25294a52\x0d\n", bfv),
      lc_ctrl_state_pkg::LcStRma:           $sformatf("BFV:%0s\x0d\nLCV:2739ce73\x0d\n", bfv)};

  virtual task check_rom_console_messages();
    // Wait for SRAM initialization to be done before hooking up the UART agent to prevent
    // X's propagating as a result of multiple drivers on pins IOC3 and IOC4 (due to DFT strap
    // sampling in TestUnlocked* and RMA lifecycel states).
    `DV_WAIT(sram_init_done_event.triggered)
    lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();
    check_uart_output_msg(exp_boot_fault_msgs[lc_state]);
  endtask

endclass : chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq
