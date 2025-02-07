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

    gpio_strap_monitor   strap_monitor;
    gpio_strap_driver    strap_driver;
    uvm_sequencer #(gpio_seq_item)  strap_sqr;
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

        // Instantiate the sequencer
        strap_sqr = uvm_sequence #(gpio_seq_item)::type_id::create("strap_sqr", this);

    endfunction : build_phase

    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        // Connect the driver to the sequencer
        strap_driver.seq_item_port.connect(strap_sqr.seq_item_export);
    endfunction : connect_phase

endclass : gpio_strap_agent

`endif // GPIO_STRAP_AGENT_SV