// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable intercept to test these commands processed in spi_device module
// - status, read jedec, read fsdp, read mailbox
class spi_device_intercept_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_intercept_vseq)
  `uvm_object_new

  // can override this queue to increase the chance to test these opcodes in extended vseq
  bit [7:0] target_ops[$] = {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3,
                             READ_JEDEC,
                             READ_SFDP,
                             READ_CMD_LIST};

  rand bit use_target_op;
  constraint opcode_c {
    solve use_target_op before opcode;
    if (use_target_op) {
      opcode inside {target_ops};
    } else {
      opcode inside {valid_opcode_q} &&
      !(opcode inside {target_ops});
    }
  }

  constraint mailbox_addr_size_c {
    read_addr_size_type == ReadAddrWithinMailbox;
  }

  virtual task pre_start();
    allow_intercept = 1;
    super.pre_start();
  endtask

  // randomly set flash_status for every spi transaction
  virtual task spi_host_xfer_flash_item(bit [7:0] op, uint payload_size,
                                        bit [31:0] addr, bit wait_on_busy = 1);
    random_access_flash_status();
    super.spi_host_xfer_flash_item(op, payload_size, addr, wait_on_busy);
  endtask
endclass : spi_device_intercept_vseq
