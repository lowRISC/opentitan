// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// 50% to send read cmd to test mailbox, especially test read cross mailbox
// boundary. This seq tests both flash mode and passthrough mode
class spi_device_mailbox_vseq extends spi_device_intercept_vseq;
  `uvm_object_utils(spi_device_mailbox_vseq)
  `uvm_object_new
  rand bit use_read_cmd;

  // high change to send read cmd
  constraint opcode_addition_c {
    solve use_read_cmd before opcode;
    if (use_read_cmd) {
      opcode inside {READ_CMD_LIST};
    } else {
      !(opcode inside {READ_CMD_LIST});
    }
  }

  // override to enable boundary cross read
  constraint mailbox_addr_size_c {
    solve read_addr_size_type before payload_size;

    read_addr_size_type dist {
      ReadAddrWithinMailbox      :/ 1,
      ReadAddrCrossIntoMailbox   :/ 2,
      ReadAddrCrossOutOfMailbox  :/ 2,
      ReadAddrCrossAllMailbox    :/ 2,
      ReadAddrOutsideMailbox     :/ 1
    };
  }

  virtual task pre_start();
    // always set both mailbox enables
    cfg_mailbox_en_pct = 100;
    intercept_mailbox_en_pct = 100;
    super.pre_start();
  endtask
endclass : spi_device_mailbox_vseq
