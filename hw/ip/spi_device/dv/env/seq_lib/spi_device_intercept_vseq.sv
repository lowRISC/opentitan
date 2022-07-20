// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable intercept to test these commands processed in spi_device module
// - status, read jedec, read fsdp, read mailbox
class spi_device_intercept_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_intercept_vseq)
  `uvm_object_new
  bit [7:0] intercept_ops[$] = {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3};

  virtual task spi_device_flash_pass_init(device_mode_e mode);
    super.spi_device_flash_pass_init( mode);

    ral.intercept_en.set(1);
    csr_update(ral.intercept_en);
  endtask

  virtual function bit [7:0] get_rand_opcode();
    bit use_intercept_op = $urandom_range(0, 1);
    bit [7:0] op;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(op,
        if (use_intercept_op) {
          op inside {intercept_ops};
        } else {
          op inside {valid_opcode_q} &&
          !(op inside {intercept_ops});
        })
    `uvm_info(`gfn, $sformatf("Sending op: 0x%0h, intercept: %0d", op, use_intercept_op),
          UVM_MEDIUM)
    return op;
  endfunction

  // randomly set flash_status for every spi transaction
  virtual task spi_host_xfer_flash_item(bit [7:0] op, uint payload_size);
    random_write_flash_status();
    super.spi_host_xfer_flash_item(op, payload_size);
  endtask
endclass : spi_device_intercept_vseq
