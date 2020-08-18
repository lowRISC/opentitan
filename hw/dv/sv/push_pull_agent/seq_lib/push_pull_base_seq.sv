// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_base_seq #(parameter int DataWidth = 32) extends dv_base_seq #(
    .REQ         (push_pull_item#(DataWidth)),
    .CFG_T       (push_pull_agent_cfg#(DataWidth)),
    .SEQUENCER_T (push_pull_sequencer#(DataWidth))
  );
  `uvm_object_param_utils(push_pull_base_seq#(DataWidth))

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
