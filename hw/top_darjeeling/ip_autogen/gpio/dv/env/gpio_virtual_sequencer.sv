// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_virtual_sequencer #(type CFG_T      = gpio_env_cfg,
                               type COV_T      = gpio_env_cov,
                               type ITEM_T     = uvm_sequence_item,
                               type RSP_ITEM_T = uvm_sequence_item)
                               extends cip_base_virtual_sequencer #(CFG_T, COV_T);

  `uvm_component_param_utils(gpio_virtual_sequencer #(CFG_T,
                                                      COV_T,
                                                      ITEM_T,
                                                      RSP_ITEM_T))

  // These fifos collects items when req/rsp is received, which are used to communicate between
  // monitor and sequences. These fifos are optional
  // When device is re-active, it gets items from req_analysis_fifo and send rsp to driver
  // When this is a high-level agent, monitors put items to these 2 fifos for high-level seq
  // This is required to be declared here as similar with dv_base_sequencer.sv to avoid compilation issues
  // when tries to reuse the dv_base_agent. TODO: Find a better solution if is possible.
  uvm_tlm_analysis_fifo #(ITEM_T)     req_analysis_fifo;
  uvm_tlm_analysis_fifo #(RSP_ITEM_T) rsp_analysis_fifo;

  function new(string name = "gpio_virtual_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

endclass
