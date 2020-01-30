// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${name}_base_seq extends dv_base_seq #(
    .REQ         (${name}_item),
    .CFG_T       (${name}_agent_cfg),
    .SEQUENCER_T (${name}_sequencer)
  );
  `uvm_object_utils(${name}_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
