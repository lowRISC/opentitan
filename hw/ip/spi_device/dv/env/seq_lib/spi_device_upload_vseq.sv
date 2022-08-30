// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable upload to test cmd upload and busy bit
class spi_device_upload_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_upload_vseq)
  `uvm_object_new

  virtual task pre_start();
    allow_upload = 1;
    // addr 3b/4b mode affects upload, as it determines how many bytes the address are.
    allow_addr_cfg_cmd = 1;
    super.pre_start();
  endtask

  virtual task body();
    bit main_seq_done;
    fork
      // this thread runs until the main_seq completes
      while (!main_seq_done) upload_fifo_read_seq();
      // main seq that sends spi items
      begin
        super.body();
        // add some delay to allow interrupt to be sent and captured in another thread.
        cfg.clk_rst_vif.wait_clks(100);
        main_seq_done = 1;
      end
    join
  endtask : body
endclass : spi_device_upload_vseq
