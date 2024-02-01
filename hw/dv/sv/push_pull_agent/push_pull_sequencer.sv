// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_sequencer #(parameter int HostDataWidth = 32,
                            parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_sequencer #(
    .ITEM_T (push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T  (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth))
);
  `uvm_component_param_utils(push_pull_sequencer#(HostDataWidth, DeviceDataWidth))
  `uvm_component_new

endclass
