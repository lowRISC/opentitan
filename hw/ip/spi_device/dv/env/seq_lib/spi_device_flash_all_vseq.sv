// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable all passthrough/flash related features during init, and then randomly send valid commands
class spi_device_flash_all_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_flash_all_vseq)
  `uvm_object_new

  int write_flash_status_pct = 30;

  constraint device_mode_c {
    device_mode inside {PassthroughMode, FlashMode};
  }

  virtual task body();
    bit main_seq_done;

    allow_addr_swap    = 1;
    allow_payload_swap = 1;
    allow_intercept    = 1;

    // enable upload
    allow_upload = 1;
    always_set_busy_when_upload_contain_payload = 1;

    allow_write_enable_disable = 1;
    allow_addr_cfg_cmd = 1;

    forever_read_buffer_update_nonblocking();
    fork
      // this thread runs until the main_seq completes
      while (!main_seq_done) upload_fifo_read_seq();
      // main seq that sends spi items
      begin
        main_seq();
        main_seq_done = 1;
      end
    join
  endtask : body

  virtual task main_seq();
    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, $sformatf("running iteration %0d/%0d", i, num_trans), UVM_LOW)

      spi_device_flash_pass_init();
      for (int j = 0; j < 20; ++j) begin
        if ($urandom_range(0, 99) < write_flash_status_pct) begin
          random_access_flash_status(.write(1), .busy(1));
        end else if ($urandom_range(0, 1)) begin
          random_access_flash_status(.write(0));
        end

        if ($urandom_range(0, 1)) read_and_check_4b_en();

        randomize_op_addr_size();
        `uvm_info(`gfn, $sformatf("Testing op_num %0d/20, op = 0x%0h", j, opcode), UVM_MEDIUM)

        spi_host_xfer_flash_item(opcode, payload_size, read_start_addr);
        cfg.clk_rst_vif.wait_clks(10);
      end
    end
  endtask : main_seq
endclass : spi_device_flash_all_vseq
