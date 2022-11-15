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
  ibex_cosim_agent               cosim_agent;
  core_ibex_vseqr                vseqr;
  core_ibex_env_cfg              cfg;
  scrambling_key_agent           scrambling_key_agent_h;
  core_ibex_scoreboard           scoreboard;

  `uvm_component_utils(core_ibex_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(core_ibex_env_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(get_full_name(), "Cannot get cfg")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_if",
                                                 cfg.ibex_clk_vif)) begin
      `uvm_fatal(`gfn, "failed to get ibex clk_if from uvm_config_db")
    end
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(this, "", "dut_if",
                                                             cfg.ibex_dut_vif)) begin
      `uvm_fatal(`gfn, "failed to get ibex dut_if from uvm_config_db")
    end
    data_if_response_agent = ibex_mem_intf_response_agent::type_id::
                          create("data_if_response_agent", this);
    instr_if_response_agent = ibex_mem_intf_response_agent::type_id::
                           create("instr_if_response_agent", this);
    irq_agent = irq_request_agent::type_id::create("irq_agent", this);
    cosim_agent = ibex_cosim_agent::type_id::create("cosim_agent", this);

    scrambling_key_agent_h = scrambling_key_agent::type_id::create("scrambling_key_agent_h", this);
    uvm_config_db#(scrambling_key_agent_cfg)::set(this, "scrambling_key_agent_h", "cfg",
                                                  cfg.scrambling_key_cfg);
    cfg.scrambling_key_cfg.agent_type = push_pull_agent_pkg::PullAgent;
    cfg.scrambling_key_cfg.if_mode = dv_utils_pkg::Device;
    // Create virtual sequencer
    vseqr = core_ibex_vseqr::type_id::create("vseqr", this);
    // Create scoreboard
    scoreboard = core_ibex_scoreboard::type_id::create("scoreboard", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    vseqr.data_if_seqr = data_if_response_agent.sequencer;
    vseqr.instr_if_seqr = instr_if_response_agent.sequencer;
    vseqr.irq_seqr = irq_agent.sequencer;
    data_if_response_agent.monitor.item_collected_port.connect(
      cosim_agent.dmem_port);
    instr_if_response_agent.monitor.item_collected_port.connect(
      cosim_agent.imem_port);
    if (cfg.enable_double_fault_detector) begin
      cosim_agent.rvfi_monitor.item_collected_port.connect(
        scoreboard.rvfi_port.analysis_export);
    end
  endfunction : connect_phase

  function void reset();
    data_if_response_agent.reset();
    instr_if_response_agent.reset();
    cosim_agent.reset();
  endfunction

endclass
