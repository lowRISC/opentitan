// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rom_e2e_shutdown_exception_c_vseq extends chip_sw_rom_e2e_shutdown_output_vseq;
  `uvm_object_utils(chip_sw_rom_e2e_shutdown_exception_c_vseq)
  `uvm_object_new

  // This matches the expected value in `sw/device/silicon_creator/rom/e2e/BUILD`. Note,
  // SystemVerilog does not support "\r" carriage return in a string literal, so we use the hex code
  // of "\x0d" instead.
  string exp_boot_fault_msg = "BFV:01495202\x0d\nLCV:2739ce73\x0d\n";

  virtual task check_rom_console_messages();
    // Wait for SRAM initialization to be done before hooking up the UART agent to prevent
    // X's propagating as a result of multiple drivers on pins IOC3 and IOC4 (due to DFT strap
    // sampling in TestUnlocked* and RMA lifecycel states).
    `DV_WAIT(sram_init_done_event.triggered)

    check_uart_output_msg(exp_boot_fault_msg);
  endtask

endclass : chip_sw_rom_e2e_shutdown_exception_c_vseq
