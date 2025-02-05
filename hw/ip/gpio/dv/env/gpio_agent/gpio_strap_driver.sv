// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_STRAP_DRIVER_SV
`define GPIO_STRAP_DRIVER_SV
class gpio_strap_driver extends dv_base_driver #(.ITEM_T(gpio_seq_item),
                                                 .CFG_T(gpio_strap_agent_cfg));
                                               // .RSP_ITEM_T(gpio_seq_item));
    `uvm_component_utils(gpio_strap_driver)

    straps_vif straps_vif_inst;
    // clk_rst virtual interface
    virtual clk_rst_if clk_rst_vif;
    

    // Constructor: Creates a new instance of the gpio_driver class
    // @param name - The name of the component
    // @param parent - The parent component
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", straps_vif_inst)) begin
            `uvm_fatal("gpio_strap_driver", "Virtual interface straps_vif_inst is not set")
        end
        if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif", clk_rst_vif)) begin
            `uvm_fatal("gpio_strap_driver", "Could not get clk_rst_vif")
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        forever begin
            gpio_seq_item m_item;
            `uvm_info("gpio_strap_driver", $sformatf("Wait for item from sequencer"), UVM_LOW)
            seq_item_port.get_next_item(m_item);
            drive_item(m_item);
            seq_item_port.item_done();
        end
    endtask

    virtual task drive_item(gpio_seq_item m_item);
        @(posedge clk_rst_vif.clk);
        straps_vif_inst.port_out.strap_en <= m_item.strap_en_i;
    endtask

endclass
`endif // GPIO_STRAP_DRIVER_SV
