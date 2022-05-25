// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// ibex processor core environment class
// ---------------------------------------------
class core_ibex_env extends uvm_env;

  ibex_mem_intf_response_agent   data_if_response_agent;
  ibex_mem_intf_response_agent   instr_if_response_agent;
  irq_request_agent              irq_agent;
`ifdef INC_IBEX_COSIM
  ibex_cosim_agent               cosim_agent;
`endif
  core_ibex_vseqr                vseqr;
  core_ibex_env_cfg              cfg;

  `uvm_component_utils(core_ibex_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(core_ibex_env_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(get_full_name(), "Cannot get cfg")
    end
    data_if_response_agent = ibex_mem_intf_response_agent::type_id::
                          create("data_if_response_agent", this);
    instr_if_response_agent = ibex_mem_intf_response_agent::type_id::
                           create("instr_if_response_agent", this);
    irq_agent = irq_request_agent::type_id::create("irq_agent", this);

`ifdef INC_IBEX_COSIM
    if (!cfg.disable_cosim) begin
      cosim_agent = ibex_cosim_agent::type_id::create("cosim_agent", this);
    end else begin
      cosim_agent = null;
    end
`endif
    // Create virtual sequencer
    vseqr = core_ibex_vseqr::type_id::create("vseqr", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    vseqr.data_if_seqr = data_if_response_agent.sequencer;
    vseqr.instr_if_seqr = instr_if_response_agent.sequencer;
    vseqr.irq_seqr = irq_agent.sequencer;

`ifdef INC_IBEX_COSIM
    if (cosim_agent != null) begin
      data_if_response_agent.monitor.item_collected_port.connect(
        cosim_agent.dmem_port);
      instr_if_response_agent.monitor.item_collected_port.connect(
        cosim_agent.imem_port);
    end
`endif
  endfunction : connect_phase

  function void reset();
    data_if_response_agent.reset();
    instr_if_response_agent.reset();
  endfunction

endclass
