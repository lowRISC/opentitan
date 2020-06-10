// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_virtual_sequencer extends cip_base_virtual_sequencer #(.CFG_T(i2c_env_cfg),
                                                                 .COV_T(i2c_env_cov));
  i2c_sequencer    i2c_sequencer_h;

  `uvm_component_utils(i2c_virtual_sequencer)
  `uvm_component_new

endclass : i2c_virtual_sequencer
