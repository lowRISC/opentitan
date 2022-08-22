// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test 4 cfg commands - wren, wrdi, en4b, ex4b
class spi_device_cfg_cmd_vseq extends spi_device_intercept_vseq;
  `uvm_object_utils(spi_device_cfg_cmd_vseq)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    target_ops = {WREN, WRDI, EN4B, EX4B};
  endfunction

  virtual task pre_start();
    allow_write_enable_disable = 1;
    allow_addr_cfg_cmd         = 1;
    super.pre_start();
  endtask

  // randomly set flash_status for every spi transaction
  virtual task spi_host_xfer_flash_item(bit [7:0] op, uint payload_size,
                                        bit [31:0] addr, bit wait_on_busy = 1);
    super.spi_host_xfer_flash_item(op, payload_size, addr, wait_on_busy);
    read_and_check_4b_en();
  endtask
endclass : spi_device_cfg_cmd_vseq
