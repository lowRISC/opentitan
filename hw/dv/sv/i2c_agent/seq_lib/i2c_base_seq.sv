// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_seq extends dv_base_seq #(
    .REQ         (i2c_item),
    .CFG_T       (i2c_agent_cfg),
    .SEQUENCER_T (i2c_sequencer)
  );
  `uvm_object_utils(i2c_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gfn, "Need to override this when you extend from this class!")
  endtask

endclass : i2c_base_seq
