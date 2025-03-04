// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_monitor extends dv_base_monitor #(.ITEM_T(uvm_sequence_item),
                                                   .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_monitor)

  // Used to send the strap outputs to the scoreboard
  uvm_analysis_port #(gpio_seq_item) mon_ap;
  // straps virtual interface
  local straps_vif m_straps_vif;
  // clk and rst virtual interface
  virtual clk_rst_if m_clk_rst_vif;
  // GPIO sequence item
  local gpio_seq_item item;
  // strap agent configuration object
  local gpio_strap_agent_cfg m_cfg;
  // gpio config env object;
  local gpio_env_cfg m_gpio_env_cfg;

  // Constructor
  function new(string name = "gpio_strap_monitor", uvm_component parent = null);
    super.new(name, parent);
    mon_ap = new ("mon_ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Agent config object
    if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "sub_cfg", m_cfg)) begin
      `uvm_fatal(`gfn, "Could not get strap agent config")
    end

    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null, "uvm_test_top.env", "cfg", m_gpio_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end

    // Get the vif handles from the environment config object.
    m_straps_vif  = m_gpio_env_cfg.straps_vif_inst;
    m_clk_rst_vif = m_gpio_env_cfg.clk_rst_vif;

    // Required because the parent class use the agent configuration object.
    super.cfg = m_cfg;
  endfunction

  // Monitor the gpio straps enable signal
  // and send the strap ouput information
  // to the scoreboard to be checked.
  virtual task run_phase(uvm_phase phase);
    forever begin : monitor_gpio_straps
      @(posedge m_clk_rst_vif.clk)
      // Only sends the item if the stran_en is posedged
      // to avoid sending items every clock cycle after the stran_en is high.
      @(posedge m_straps_vif.tb_port.strap_en) begin
        // Wait for at least 2 clock cycles after strap_en is asserted.
        // to get the registers ready.
        m_clk_rst_vif.wait_clks(2);
        // Check if the reset operation is completed.
        if (m_clk_rst_vif.rst_n) begin
          // Sample the strap data and valid
          item = new();
          item.sampled_straps_o.data  = m_straps_vif.tb_port.sampled_straps.data;
          item.sampled_straps_o.valid = m_straps_vif.tb_port.sampled_straps.valid;
          // Send the sampled straps to the gpio scoreboard.
          mon_ap.write(item);
        end
      end
    end
  endtask
endclass : gpio_strap_monitor
