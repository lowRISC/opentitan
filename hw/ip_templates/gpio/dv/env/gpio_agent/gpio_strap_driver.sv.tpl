// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_driver extends dv_base_driver #(.ITEM_T(uvm_sequence_item),
  .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_driver)

  gpio_env_cfg           m_env_cfg;
  // Constructor: Creates a new instance of the gpio_driver class
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null, "uvm_test_top.env", "cfg", m_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end
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
    @(posedge m_env_cfg.clk_rst_vif.clk or m_env_cfg.under_reset);
    m_env_cfg.m_straps_vif.tb_port.strap_en <= req.strap_en_i;
  endtask
endclass
