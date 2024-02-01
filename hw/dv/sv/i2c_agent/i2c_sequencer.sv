// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_sequencer extends dv_base_sequencer#(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_sequencer)
  `uvm_component_new

endclass : i2c_sequencer
