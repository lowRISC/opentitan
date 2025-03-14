// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_strap_agent extends dv_base_agent  #(.CFG_T(${module_instance_name}_strap_agent_cfg),
                                                .DRIVER_T(${module_instance_name}_strap_driver),
                                                .SEQUENCER_T(strap_sequencer),
                                                .MONITOR_T(${module_instance_name}_strap_monitor));

  `uvm_component_utils(${module_instance_name}_strap_agent)

  extern function new(string name, uvm_component parent);

  ${module_instance_name}_strap_monitor     strap_monitor;
  ${module_instance_name}_strap_driver      strap_driver;
  strap_sequencer        strap_sqr;
  ${module_instance_name}_strap_agent_cfg   cfg;

  function void build_phase(uvm_phase phase);

    // Instantiate the monitor
    strap_monitor = ${module_instance_name}_strap_monitor::type_id::create("strap_monitor", this);
    // Instantiate the driver
    strap_driver = ${module_instance_name}_strap_driver::type_id::create("strap_driver", this);
    // Instantiate the sequencer
    strap_sqr = strap_sequencer::type_id::create("strap_sqr", this);
    // Set the sequencer in the config DB for the driver
    uvm_config_db#(strap_sequencer)::set(this, "*", "strap_sqr", strap_sqr);

    // Instantiate the strap agent config object
    cfg = ${module_instance_name}_strap_agent_cfg::type_id::create("cfg", this);

    // Set the agent cfg in the config DB
    uvm_config_db#(${module_instance_name}_strap_agent_cfg)::set(this, "", "cfg", cfg);
    // Set the agent cfg in the config DB that is used in the strap monitor and driver.
    uvm_config_db#(${module_instance_name}_strap_agent_cfg)::set(this, "*", "sub_cfg", cfg);

    super.build_phase(phase);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    strap_driver.seq_item_port.connect(strap_sqr.seq_item_export);
    super.connect_phase(phase);
  endfunction : connect_phase

endclass : ${module_instance_name}_strap_agent

function ${module_instance_name}_strap_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction