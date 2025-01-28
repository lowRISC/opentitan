// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef GPIO_STRAP_MONITOR_SV
`define GPIO_STRAP_MONITOR_SV

class gpio_strap_monitor extends dv_base_monitor #(.ITEM_T(gpio_seq_item),
                                                   .CFG_T(gpio_strap_agent_cfg));

    `uvm_component_utils(gpio_strap_monitor)

    uvm_analysis_port  #(gpio_seq_item) mon_ap;
    straps_vif straps_vif_inst;
    // gpio virtual interface
    gpio_vif gpio_vif_inst;
    // clk_rst virtual interface
    virtual clk_rst_if clk_rst_vif;
    gpio_seq_item item;
    

    // Constructor
    function new(string name = "gpio_strap_monitor", uvm_component parent = null);
        super.new(name, parent);
        mon_ap = new ("mon_ap", this);
        item = new();
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", straps_vif_inst)) begin
            `uvm_fatal("gpio_strap_monitor", "Virtual interface straps_vif_inst is not set")
        end
        if (!uvm_config_db#(virtual pins_if #(NUM_GPIOS))::get(this, "*.env", "gpio_vif", gpio_vif_inst)) begin
          `uvm_fatal("gpio_strap_monitor", "Could not get gpio_vif")
        end
        if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif", clk_rst_vif)) begin
            `uvm_fatal("gpio_strap_monitor", "Could not get clk_rst_vif")
        end
      endfunction

    // Task to monitor GPIO strap signals
    virtual task run_phase(uvm_phase phase);
        fork
            monitor_gpio_straps();
        join_none
    endtask

    // Task: monitor_gpio_straps
    // The task monitors the gpio straps enable signal
    // and checks the straps output signal after the first strap trigger
    virtual task monitor_gpio_straps();
        forever begin : monitor_gpio_straps
            @(posedge clk_rst_vif.clk)
            if(!clk_rst_vif.rst_n) begin
                if (|gpio_vif_inst.pins === 1'b1) begin
                    @(posedge straps_vif_inst.port_out.strap_en) begin
                        // Wait for at least 1 clock cycle after strap_en is asserted, to allow the straps to be
                        // ready for sampling.
                        clk_rst_vif.wait_clks(1);
                        // Sample the straps
                        item.sampled_straps_o.data  = straps_vif_inst.port_out.sampled_straps.data;
                        item.sampled_straps_o.valid = straps_vif_inst.port_out.sampled_straps.valid;
                        // Send the sampled straps to the analysis port
                        mon_ap.write(item);
                    end
                end
            end
        end
    endtask : monitor_gpio_straps
endclass : gpio_strap_monitor
`endif // GPIO_STRAP_MONITOR_SV