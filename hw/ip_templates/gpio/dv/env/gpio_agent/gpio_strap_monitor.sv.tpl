// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_strap_monitor extends dv_base_monitor #(.ITEM_T(uvm_sequence_item),
                                                   .CFG_T(${module_instance_name}_strap_agent_cfg));

  `uvm_component_utils(${module_instance_name}_strap_monitor)

  // Used to send the strap outputs to the scoreboard
  uvm_analysis_port #(${module_instance_name}_seq_item) mon_ap;
  // gpio data pin interface
  local gpio_vif m_gpio_vif;
  // straps virtual interface
  local straps_vif m_straps_vif;
  // clk and rst virtual interface
  virtual clk_rst_if m_clk_rst_vif;
  // GPIO sequence item
  local ${module_instance_name}_seq_item item;
  // strap agent configuration object
  local ${module_instance_name}_strap_agent_cfg m_cfg;
  // ${module_instance_name} config env object;
  local ${module_instance_name}_env_cfg m_${module_instance_name}_env_cfg;

  // Constructor
  function new(string name = "${module_instance_name}_strap_monitor", uvm_component parent = null);
    super.new(name, parent);
    mon_ap = new ("mon_ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Agent config object
    if (!uvm_config_db#(${module_instance_name}_strap_agent_cfg)::get(this, "", "sub_cfg", m_cfg)) begin
      `uvm_fatal(`gfn, "Could not get strap agent config")
    end

    // Environment config object.
    if (!uvm_config_db#(${module_instance_name}_env_cfg)::get(null, "uvm_test_top.env", "cfg", m_${module_instance_name}_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end

    // Get the vif handles from the environment config object.
    m_gpio_vif    = m_${module_instance_name}_env_cfg.gpio_vif;
    m_straps_vif  = m_${module_instance_name}_env_cfg.straps_vif_inst;
    m_clk_rst_vif = m_${module_instance_name}_env_cfg.clk_rst_vif;

    // Required because the parent class use the agent configuration object.
    super.cfg = m_cfg;
  endfunction

  // Monitor the ${module_instance_name} straps enable signal
  // and send the strap ouput information
  // to the scoreboard to be checked.
  virtual task run_phase(uvm_phase phase);
    forever begin : monitor_${module_instance_name}_straps
      @(posedge m_clk_rst_vif.clk or negedge m_clk_rst_vif.rst_n)
      item = new();
      // Sample the strap data and valid
      `uvm_info(`gfn, "Send the strap data and valid zero values after reset.", UVM_HIGH)
      item.strap_en_i             = m_straps_vif.strap_en;
      item.cio_gpio_i             = m_gpio_vif.pins;
      item.sampled_straps_o.data  = m_straps_vif.tb_port.sampled_straps.data;
      item.sampled_straps_o.valid = m_straps_vif.tb_port.sampled_straps.valid;
      // Send the sampled straps to the ${module_instance_name} scoreboard.
      mon_ap.write(item);
    end
  endtask
endclass : ${module_instance_name}_strap_monitor