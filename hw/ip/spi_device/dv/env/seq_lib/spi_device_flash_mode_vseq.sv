// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// set mode to FlashMode to test read buffer along with other intercept commands
class spi_device_flash_mode_vseq extends spi_device_intercept_vseq;
  `uvm_object_utils(spi_device_flash_mode_vseq)
  `uvm_object_new

  constraint device_mode_c {
    device_mode == FlashMode;
  }

  function void pre_randomize();
    super.pre_randomize();
    target_ops = {READ_CMD_LIST};
  endfunction

  constraint num_trans_c {
    num_trans inside {[20:30]};
  }

  task body();
    // increase the chance (15%->50%) to send large payload,
    // in order to exercise watermark and flip events
    large_payload_weight = 6;

    // always read the last_read_addr for check
    read_last_read_addr_pct = 100;

    mailbox_addr_size_c.constraint_mode(0);
    forever_read_buffer_update_nonblocking();

    allow_set_cmd_info_invalid = 1;
    allow_use_invalid_opcode = 1;
    spi_device_flash_pass_init();

    for (int i = 0; i < num_trans; ++i) begin
      randomize_op_addr_size();
      `uvm_info(`gfn, $sformatf("sending op 0x%0h addr: 0x%0x", opcode, read_start_addr),
                UVM_MEDIUM)
      spi_host_xfer_flash_item(opcode, payload_size, read_start_addr);
    end
  endtask
endclass : spi_device_flash_mode_vseq
