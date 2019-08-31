// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_base_seq extends uvm_sequence#(spi_item);
  `uvm_object_utils(spi_base_seq)
  `uvm_declare_p_sequencer(spi_sequencer)

  `uvm_object_new

  task body();
    `uvm_error(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
