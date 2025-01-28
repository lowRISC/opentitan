// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_BASE_SEQUENCER_SV
`define GPIO_BASE_SEQUENCER_SV

class gpio_base_sequencer #(type ITEM_T     = gpio_seq_item, 
                            type CFG_T      = gpio_strap_agent_cfg,
                            type RSP_ITEM_T = gpio_seq_item) extends dv_base_sequencer #(ITEM_T, CFG_T, RSP_ITEM_T);

    `uvm_component_param_utils(gpio_base_sequencer #(ITEM_T, CFG_T, RSP_ITEM_T))

    gpio_strap_agent_cfg cfg;
    uvm_sequencer #(gpio_seq_item) strap_sqr_h;

    function new(string name = "gpio_base_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);
        
        // Retrieve agent configuration
        if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("gpio_base_sequencer", "Agent config not found in uvm_config_db!")
        end
        // Passing the cfg handle from the gpio_base_sequencer to the dv_base_sequencer
        super.cfg = cfg;

        // Instantiate the sequencer strap
        strap_sqr_h = uvm_sequence #(gpio_seq_item)::type_id::create("strap_sqr_h", this);

        super.build_phase(phase);
    endfunction : build_phase
endclass
`endif // GPIO_BASE_SEQUENCER_SV