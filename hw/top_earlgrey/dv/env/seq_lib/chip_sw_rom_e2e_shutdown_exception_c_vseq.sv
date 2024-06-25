// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_shutdown_exception_c_vseq extends chip_sw_rom_e2e_base_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_shutdown_exception_c_vseq)
  `uvm_object_new

  virtual task body();
    super.body();
    connect_rom_uart_agent();
    check_uart_output_msg($sformatf("%0s\x0d\n", ROM_BANNER));
    check_uart_output_msg($sformatf("BFV:%0s\x0d\nLCV:%0s\x0d",
      ROM_BFV_INSTRUCTION_ACCESS, ROM_LCV_RMA));
    disconnect_rom_uart_agent();
    rom_e2e_test_boot_fault_success();
  endtask

endclass : chip_sw_rom_e2e_shutdown_exception_c_vseq
