// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_base_seq #(parameter int HostDataWidth = 32,
                           parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_seq #(
    .REQ         (push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T       (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)),
    .SEQUENCER_T (push_pull_sequencer#(HostDataWidth, DeviceDataWidth))
  );
  `uvm_object_param_utils(push_pull_base_seq#(HostDataWidth, DeviceDataWidth))

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
