// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_virtual_sequencer #(parameter int AddrWidth = 10) extends cip_base_virtual_sequencer
  #(.CFG_T(sram_ctrl_env_cfg#(AddrWidth)),
    .COV_T(sram_ctrl_env_cov#(AddrWidth))
  );
  `uvm_component_param_utils(sram_ctrl_virtual_sequencer#(AddrWidth))

  `uvm_component_new

endclass
