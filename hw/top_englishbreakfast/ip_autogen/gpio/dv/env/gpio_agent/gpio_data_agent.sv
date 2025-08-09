// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_data_agent extends dv_base_agent #(
  .CFG_T(gpio_data_agent_cfg),
  .DRIVER_T(gpio_data_driver),
  .SEQUENCER_T(dv_base_sequencer),
  .MONITOR_T(gpio_data_monitor)
  );

  `uvm_component_utils(gpio_data_agent)

  extern function new(string name, uvm_component parent);

  gpio_data_monitor     data_monitor;
  gpio_data_driver      data_driver;
  gpio_data_agent_cfg   cfg;

  function void build_phase(uvm_phase phase);

    // Instantiate the monitor
    data_monitor = gpio_data_monitor::type_id::create("data_monitor", this);
    // Instantiate the driver
    data_driver = gpio_data_driver::type_id::create("data_driver", this);
    // Instantiate the data_in agent config object
    cfg = gpio_data_agent_cfg::type_id::create("cfg", this);

    // Set the agent cfg in the config DB
    uvm_config_db#(gpio_data_agent_cfg)::set(this, "", "cfg", cfg);
    // Set the agent cfg in the config DB that is used in the data_in monitor and driver.
    uvm_config_db#(gpio_data_agent_cfg)::set(this, "*", "sub_cfg", cfg);

    super.build_phase(phase);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction : connect_phase

endclass : gpio_data_agent

function gpio_data_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction
