// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_driver extends dv_base_driver #(.ITEM_T(uvm_sequence_item),
                                                 .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_driver)

  // Strap interface used to trigger the strap_en_i signal.
  local straps_vif m_straps_vif;
  // Clock and reset virtual interface
  virtual local clk_rst_if m_clk_rst_vif;
  // Strap virtual sequencer used to get the gpio seq items
  local strap_sequencer    m_seqr;
  // gpio config env object;
  gpio_env_cfg m_gpio_env_cfg;

  // Constructor: Creates a new instance of the gpio_driver class
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Strap sequencer uvm_config_db get method.
    if (!uvm_config_db#(strap_sequencer)::get(this, "", "strap_sqr", m_seqr)) begin
        `uvm_fatal(`gfn, "Failed to get sequencer handle from config DB!")
    end
    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null,
                                                              "uvm_test_top.env",
                                                              "cfg",
                                                              m_gpio_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end

    // Get the vif handles from the environment config object.
    m_straps_vif   = m_gpio_env_cfg.straps_vif_inst;
    m_clk_rst_vif  = m_gpio_env_cfg.clk_rst_vif;
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      gpio_seq_item m_item;
      seq_item_port.get_next_item(req);

      if(!$cast(m_item , req)) begin
          `uvm_error("gpio_strap_driver", "Failed to cast item to gpio_seq_item")
      end
      `uvm_info(`gfn, "Drive strap_en signal", UVM_HIGH)
      drive_item(m_item);
      seq_item_port.item_done();
    end
  endtask

  // Drive the strap_en_i pin
  task drive_item(gpio_seq_item req);
    @(posedge m_clk_rst_vif.clk);
    wait(!m_gpio_env_cfg.under_reset);
    m_straps_vif.tb_port.strap_en <= req.strap_en_i;
  endtask
endclass
