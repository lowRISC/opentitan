// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable all passthrough related features during init, and then randomly send valid commands
class spi_device_pass_all_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_all_vseq)
  `uvm_object_new

  int write_flash_status_pct = 30;
  virtual task body();
    allow_addr_swap    = 1;
    allow_payload_swap = 1;
    allow_intercept    = 1;

    for (int i = 0; i < num_trans; ++i) begin
      `uvm_info(`gfn, $sformatf("running iteration %0d/%0d", i, num_trans), UVM_LOW)
      spi_device_flash_pass_init(PassthroughMode);

      for (int j = 0; j < 20; ++j) begin
        if ($urandom_range(0, 99) < write_flash_status_pct) random_write_flash_status();

        randomize_op_addr_size();
        `uvm_info(`gfn, $sformatf("Testing op_num %0d/20, op = 0x%0h", j, opcode), UVM_MEDIUM)

        spi_host_xfer_flash_item(opcode, payload_size, read_start_addr);
        cfg.clk_rst_vif.wait_clks(10);
      end
    end

  endtask : body
endclass : spi_device_pass_all_vseq
