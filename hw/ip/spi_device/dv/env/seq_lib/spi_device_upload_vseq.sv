// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable upload to test cmd upload and busy bit
class spi_device_upload_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_upload_vseq)
  `uvm_object_new

  virtual task pre_start();
    allow_upload = 1;
    super.pre_start();
  endtask

  virtual task spi_host_wait_on_busy();
    // read fifo and clear busy
    read_upload_fifos();

    // issue read status to actually clear the busy bit
    super.spi_host_wait_on_busy();
  endtask

  virtual task body();
    super.body();
    read_upload_fifos();
  endtask : body
endclass : spi_device_upload_vseq
