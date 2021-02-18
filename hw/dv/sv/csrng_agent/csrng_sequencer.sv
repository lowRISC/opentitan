// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_sequencer extends dv_base_sequencer #(
    .ITEM_T (csrng_item),
    .CFG_T  (csrng_agent_cfg)
);
  `uvm_component_param_utils(csrng_sequencer)

  // Analysis port through which device monitors can send transactions
  // to the sequencer.
  uvm_tlm_analysis_fifo#(csrng_item) csrng_req_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      csrng_req_fifo = new("csrng_req_fifo", this);
    end
  endfunction

endclass
