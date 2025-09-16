// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The base config object for an agent

class dv_base_agent_cfg extends uvm_object;

  // True if this is an active agent, so has a driver and sequencer. If false, this is a passive
  // agent and only uses a monitor.
  bit is_active = 1'b1;

  // True if the agent should enable a monitor (perhaps for a scoreboard)
  bit en_monitor = 1'b1;

  // True if the agent should collect functional coverage
  bit en_cov = 1'b1;

  // Relevant for an agent that acts on a communication bus. This is the interface mode of the agent
  // on the bus. If if_mode == dv_utils_pkg::Device, the dut is assumed to be a host to which the
  // agent responds. If if_mode == dv_utils_pkg::Host, the dut is assumed to be a device which will
  // respond to transactions from the agent.
  if_mode_e if_mode;

  // True if the agent has its own driver, which should be attached to the sequencer. If this is
  // false, the agent can work by connecting to some lower-level agent to send multiple items.
  bit has_driver = 1'b1;

  // True if agent's sequencer has a request fifo. If so, the agent will connect its monitor's
  // req_analysis_port to the sequencer's request fifo.
  bit has_req_fifo = 1'b0;

  // True if agent's sequencer has a response fifo. If so, the agent will connect its monitor's
  // req_analysis_port to the sequencer's response fifo.
  bit has_rsp_fifo = 1'b0;

  // The minimum time in ns that the monitor expects to see ok_to_end be high before it drops an
  // objection that stopped the run_phase ending.
  int ok_to_end_delay_ns = 1000;

  // Indicates that the interface is under reset. The derived monitor detects and maintains it. Note
  // that this is distinct from the under_reset flag in dv_base_env_cfg: the interface of an agent
  // can be in reset even if the environment as a whole is not.
  bit in_reset;

  `uvm_object_utils_begin(dv_base_agent_cfg)
    `uvm_field_int (is_active,            UVM_DEFAULT)
    `uvm_field_int (en_monitor,           UVM_DEFAULT)
    `uvm_field_int (en_cov,               UVM_DEFAULT)
    `uvm_field_enum(if_mode_e, if_mode,   UVM_DEFAULT)
    `uvm_field_int (has_driver,           UVM_DEFAULT)
    `uvm_field_int (has_req_fifo,         UVM_DEFAULT)
    `uvm_field_int (has_rsp_fifo,         UVM_DEFAULT)
    `uvm_field_int (ok_to_end_delay_ns,   UVM_DEFAULT)
    `uvm_field_int (in_reset,             UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new (string name="");
endclass

function dv_base_agent_cfg::new (string name="");
  super.new(name);
endfunction
