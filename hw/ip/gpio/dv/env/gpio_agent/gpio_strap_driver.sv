// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_driver extends dv_base_driver #(.ITEM_T(uvm_sequence_item),
                                                 .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_driver)

  straps_vif         m_straps_vif;
  virtual clk_rst_if clk_rst_vif;
  strap_sequencer    m_seqr;

  // Constructor: Creates a new instance of the gpio_driver class
  // @param name - The name of the component
  // @param parent - The parent component
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(straps_vif)::get(this, "*.*", "straps_vif", m_straps_vif)) begin
        `uvm_fatal(`gfn, "Virtual interface m_straps_vif is not set in the uvm_config_db")
    end
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "*.env", "clk_rst_vif", clk_rst_vif)) begin
        `uvm_fatal(`gfn, "Could not get clk_rst_vif")
    end
    if (!uvm_config_db#(strap_sequencer)::get(this, "", "strap_sqr", m_seqr)) begin
        `uvm_fatal(`gfn, "Failed to get sequencer handle from config DB!")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    forever begin
      gpio_seq_item m_item;
      seq_item_port.get_next_item(req);

      if(!$cast(m_item , req)) begin
          `uvm_error("gpio_strap_driver", "Failed to cast item to gpio_seq_item")
      end
      drive_item(m_item);
      seq_item_port.item_done();
    end
  endtask

  // Drive the stran_en_i pin
  virtual task drive_item(gpio_seq_item req);
    @(posedge clk_rst_vif.clk);
    m_straps_vif.tb_if.strap_en <= req.strap_en_i;
  endtask

endclass
