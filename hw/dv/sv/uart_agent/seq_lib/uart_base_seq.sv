// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_base_seq extends uvm_sequence#(uart_item);
  `uvm_object_utils(uart_base_seq)
  `uvm_declare_p_sequencer(uart_sequencer)

  `uvm_object_new

  task body();
    `uvm_error(`gtn, "Need to override this when you extend from this class!")
  endtask : body

endclass : uart_base_seq
