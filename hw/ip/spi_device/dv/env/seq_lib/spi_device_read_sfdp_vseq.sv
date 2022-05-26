// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Read SFDP command in flash and passthrough mode
class spi_device_read_sfdp_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_read_sfdp_vseq)
  `uvm_object_new

  virtual task body();

    fork
      start_reactive_seq();
    join_none

    cfg.clk_rst_vif.wait_clks(100);

    spi_device_flash_pass_init(FlashMode);
    do_flash_pass_read(READ_SFDP);
    spi_device_flash_pass_init(PassthroughMode);
    do_flash_pass_read(READ_SFDP);

  endtask : body

endclass : spi_device_read_sfdp_vseq
