// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_STRAP_AGENT_SV
`define GPIO_STRAP_AGENT_SV
class gpio_strap_agent extends dv_base_agent  #(.CFG_T(gpio_strap_agent_cfg),
                                                .DRIVER_T(gpio_strap_driver),
                                                .SEQUENCER_T(gpio_base_sequencer),
                                                .MONITOR_T(gpio_strap_monitor));
                                              
    `uvm_component_utils(gpio_strap_agent)

    gpio_strap_monitor  strap_monitor;
    gpio_strap_driver   strap_driver;
    gpio_base_sequencer gpio_sqr;
    gpio_strap_agent_cfg cfg;
    
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Instantiate the monitor
        strap_monitor = gpio_strap_monitor::type_id::create("strap_monitor", this);
        // Instantiate the driver
        strap_driver = gpio_strap_driver::type_id::create("strap_driver", this);
        
        // Retrieve agent configuration
        if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("gpio_strap_agent", "Agent config not found in uvm_config_db!")
        end

        `uvm_info(get_full_name(), "Agent cfg get from uvm_config_db", UVM_HIGH)

        // Instantiate the sequencer
        gpio_sqr = gpio_base_sequencer::type_id::create("gpio_sqr", this);

        `uvm_info(get_full_name(), "Sequencer created", UVM_HIGH)

        // Set the gpio_sqr sequencer in the env configuration
        uvm_config_db#(gpio_base_sequencer)::set(this, "*.*", "gpio_sqr", gpio_sqr);
        
    endfunction : build_phase

    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        // Connect the driver to the sequencer
        strap_driver.seq_item_port.connect(gpio_sqr.seq_item_export);
    endfunction : connect_phase

    // Run phase
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
    endtask : run_phase

endclass : gpio_strap_agent

`endif // GPIO_STRAP_AGENT_SV