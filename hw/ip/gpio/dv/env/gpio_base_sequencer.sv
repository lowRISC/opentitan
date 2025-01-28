// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_BASE_SEQUENCER_SV
`define GPIO_BASE_SEQUENCER_SV

class gpio_base_sequencer extends dv_base_sequencer #(.ITEM_T(gpio_seq_item),
                                                      .CFG_T(gpio_strap_agent_cfg),
                                                      .RSP_ITEM_T(gpio_seq_item));
    `uvm_component_utils(gpio_base_sequencer)

    gpio_strap_agent_cfg cfg;

    function new(string name = "gpio_base_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);
        
        `uvm_info(get_full_name(), "Sequencer get the cfg in the uvm_config_db", UVM_HIGH)

        // Retrieve agent configuration
        if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("gpio_base_sequencer", "Agent config not found in uvm_config_db!")
        end

        `uvm_info(get_full_name(), $sformatf("Sequencer %s get the cfg in the uvm_config_db", cfg.get_name()), UVM_HIGH)

        if (cfg.has_req_fifo)
        `uvm_info(get_full_name(), $sformatf("%s get req fifo", cfg.get_name()), UVM_HIGH)
        if (cfg.has_rsp_fifo) rsp_analysis_fifo = new("rsp_analysis_fifo", this);
        `uvm_info(get_full_name(), $sformatf("%s get rsp fifo", cfg.get_name()), UVM_HIGH)

        super.build_phase(phase);
    endfunction : build_phase
endclass
`endif // GPIO_BASE_SEQUENCER_SV