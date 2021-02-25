// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_sequencer extends dv_base_sequencer #(
    .ITEM_T (csrng_item),
    .CFG_T  (csrng_agent_cfg)
);
  `uvm_component_param_utils(csrng_sequencer)

  push_pull_sequencer#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))          m_req_push_sequencer;
  push_pull_sequencer#(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))   m_genbits_push_sequencer;

  // Analysis port through which device monitors can send transactions
  // to the sequencer.
  uvm_tlm_analysis_fifo#(csrng_item)   cmd_req_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      cmd_req_fifo = new("cmd_req_fifo", this);
    end
  endfunction

endclass
