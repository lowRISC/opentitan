// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// drive everything 0 for testing break error
class uart_default_seq extends uart_seq;
  `uvm_object_utils(uart_default_seq)

  constraint parity_err_c {
    parity_err == 0;
  }
  constraint frame_err_c {
    frame_err == 0;
  }

  `uvm_object_new

endclass : uart_default_seq
