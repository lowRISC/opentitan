// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_data_monitor extends dv_base_monitor #(
  .ITEM_T(uvm_sequence_item),
  .CFG_T(gpio_data_agent_cfg));

  `uvm_component_utils(gpio_data_monitor)

  // Used to send the data_in outputs to the scoreboard
  uvm_analysis_port #(gpio_seq_item) mon_ap;
  // clk and rst virtual interface
  virtual clk_rst_if m_clk_rst_vif;
  // GPIO sequence item
  local gpio_seq_item item;
  // data_in agent configuration object
  local gpio_data_agent_cfg m_cfg;
  // gpio config env object;
  local gpio_env_cfg m_env_cfg;
  // gpio data in virtual interface;
  gpio_vif m_gpio_vif;

  // input presented by driving gpio_i
  logic [NUM_GPIOS-1:0] gpio_i_driven;

  // Constructor
  function new(string name = "gpio_data_in_monitor", uvm_component parent = null);
    super.new(name, parent);
    mon_ap = new ("mon_ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Agent config object
    if (!uvm_config_db#(gpio_data_agent_cfg)::get(this, "", "sub_cfg", m_cfg)) begin
      `uvm_fatal(`gfn, "Could not get data_in agent config")
    end

    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null, "uvm_test_top.env", "cfg", m_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end

    // Get the vif handles from the environment config object.
    m_clk_rst_vif = m_env_cfg.clk_rst_vif;
    m_gpio_vif    = m_env_cfg.gpio_vif;
    // Required because the parent class use the agent configuration object.
    super.cfg = m_cfg;
  endfunction

  // Monitor the gpio data_in and out pins
  // and send the information to the scoreboard to be checked.
  virtual task run_phase(uvm_phase phase);
    monitor_gpio_data();
  endtask

  // Task : monitor_gpio_i
  // monitor gpio input pins interface
  virtual task monitor_gpio_data();
    forever begin : monitor_pins_if
      @(m_gpio_vif.pins or m_env_cfg.under_reset);
      if (m_env_cfg.under_reset == 1'b0) begin
        `uvm_info(`gfn, "Sending pins data to the scoreboard", UVM_HIGH)
        item = new();
        item.pins = m_gpio_vif.pins;
        // Send the sampled gpio pins to the gpio scoreboard.
        mon_ap.write(item);
      end
    end
  endtask : monitor_gpio_data

endclass : gpio_data_monitor
