// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test 4 cfg commands - wren, wrdi, en4b, ex4b
class spi_device_cfg_cmd_vseq extends spi_device_intercept_vseq;
  `uvm_object_utils(spi_device_cfg_cmd_vseq)
  `uvm_object_new

  function void pre_randomize();
    // TODO, 2 more to add
    intercept_ops[$] = {WREN, WRDI};
  endfunction

  virtual task pre_start();
    allow_write_enable_disable = 1;
    super.pre_start();
  endtask
endclass : spi_device_cfg_cmd_vseq
