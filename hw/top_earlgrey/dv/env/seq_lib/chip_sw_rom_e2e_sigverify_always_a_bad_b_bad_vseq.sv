// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq extends
  chip_sw_rom_e2e_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq)
  `uvm_object_new

  lc_ctrl_state_pkg::lc_state_e lc_state;

  virtual task body();
    super.body();
    connect_rom_uart_agent();
    lc_state = cfg.mem_bkdr_util_h[Otp].otp_read_lc_partition_state();
    check_uart_output_msg($sformatf("%0s\x0d\n", ROM_BANNER));
    check_uart_output_msg(
      $sformatf("BFV:%0s\x0d\nLCV:%0s\x0d\n", ROM_BFV_BAD_ECDSA_SIGNATURE,
      lc_state_2_rom_lcv[lc_state]));
    disconnect_rom_uart_agent();
    rom_e2e_test_boot_fault_success();
  endtask

endclass : chip_sw_rom_e2e_sigverify_always_a_bad_b_bad_vseq
