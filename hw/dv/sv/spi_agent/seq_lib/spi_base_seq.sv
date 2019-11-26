// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_base_seq extends dv_base_seq #(
    .REQ         (spi_item),
    .CFG_T       (spi_agent_cfg),
    .SEQUENCER_T (spi_sequencer)
  );
  `uvm_object_utils(spi_base_seq)
  `uvm_object_new

  task body();
    `uvm_error(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
