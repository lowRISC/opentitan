// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_VIRTUAL_SEQUENCER_SV
`define GPIO_VIRTUAL_SEQUENCER_SV

class gpio_virtual_sequencer #(type CFG_T      = gpio_env_cfg, 
                               type COV_T      = gpio_env_cov) extends cip_base_virtual_sequencer #(CFG_T, COV_T);

    `uvm_component_param_utils(gpio_virtual_sequencer #(CFG_T, COV_T))
    function new(string name = "gpio_virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction : build_phase
endclass
`endif // GPIO_VIRTUAL_SEQUENCER_SV