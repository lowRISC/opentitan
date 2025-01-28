// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_monitor extends dv_base_monitor #(.ITEM_T(uvm_sequence_item),
                                                   .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_monitor)

  // Used to send the strap outputs to the scoreboard
  uvm_analysis_port  #(gpio_seq_item) mon_ap;
  // straps virtual interface
  straps_vif m_straps_vif;
  // gpio virtual interface
  gpio_vif m_gpio_vif;
  // clk and rst virtual interface
  virtual clk_rst_if clk_rst_vif;
  // GPIO sequence item
  gpio_seq_item item;
  // strap agent configuration object
  gpio_strap_agent_cfg cfg;

  // Constructor
  function new(string name = "gpio_strap_monitor", uvm_component parent = null);
    super.new(name, parent);
    mon_ap = new ("mon_ap", this);
    item = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", m_straps_vif)) begin
        `uvm_fatal(`gfn, "Virtual interface m_straps_vif is not set")
    end
    if (!uvm_config_db#(gpio_vif)::get(this, "*.env", "gpio_vif", m_gpio_vif)) begin
        `uvm_fatal(`gfn, "Could not get m_gpio_vif")
            end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif", clk_rst_vif)) begin
        `uvm_fatal(`gfn, "Could not get clk_rst_vif")
    end
    if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "monitor_cfg", cfg)) begin
        `uvm_fatal(`gfn, "Could not get strap agent config")
    end
    // Required because the parent class use the agent configuration object.
    super.cfg = cfg;
  endfunction

  // Task to monitor GPIO strap signals
  virtual task run_phase(uvm_phase phase);
    fork
      monitor_gpio_straps();
    join_none
  endtask

  // Task: monitor_gpio_straps
  // The task monitor the gpio straps enable signal
  // and send the strap ouput information to the scoreboard to be checked.
  virtual task monitor_gpio_straps();
    forever begin : monitor_gpio_straps
      @(posedge clk_rst_vif.clk)
      clk_rst_vif.wait_clks_or_rst(1);
      if(m_straps_vif.tb_if.strap_en &&
        !m_straps_vif.strap_en_q   &&
        !m_straps_vif.strap_en_qq) begin
        // Wait for at least 1 clock cycle after strap_en is asserted.
        clk_rst_vif.wait_clks_or_rst(1);
        if(clk_rst_vif.rst_n) begin
          // Sample the straps
          item.sampled_straps_o.data  = m_straps_vif.tb_if.sampled_straps.data;
          item.sampled_straps_o.valid = m_straps_vif.tb_if.sampled_straps.valid;
          // Send the sampled straps to the gpio scoreboard.
          mon_ap.write(item);
        end
      end
    end
  endtask : monitor_gpio_straps
endclass : gpio_strap_monitor
