// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_monitor extends dv_base_monitor #(.ITEM_T(uvm_sequence_item),
                                                   .CFG_T(gpio_strap_agent_cfg));

  `uvm_component_utils(gpio_strap_monitor)

  // Used to send the strap outputs to the scoreboard
  uvm_analysis_port #(gpio_seq_item) mon_ap;
  // gpio config env object;
  local gpio_env_cfg m_env_cfg;

  // Constructor
  function new(string name = "gpio_strap_monitor", uvm_component parent = null);
    super.new(name, parent);
    mon_ap = new ("mon_ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Agent config object
    if (!uvm_config_db#(gpio_strap_agent_cfg)::get(this, "", "sub_cfg", cfg)) begin
      `uvm_fatal(`gfn, "Could not get strap agent config")
    end

    // Environment config object.
    if (!uvm_config_db#(gpio_env_cfg)::get(null, "uvm_test_top.env", "cfg", m_env_cfg)) begin
      `uvm_fatal(`gfn, "Could not get environment config object")
    end
  endfunction

  // Monitor the strap_en signal
  // When the strap_en signal is high, sample the strap data and valid signals
  // and send them to the scoreboard to be compared with the expected values.
  // The output data strap is sampled on the outputs after 2 clock cycles.
  // One clock cycle to update the registers and one clock cycle if a reset is asserted
  // in the middle of a clock cycle.
  virtual task run_phase(uvm_phase phase);
    // GPIO sequence item
    gpio_seq_item item;
    forever begin : monitor_gpio_straps
      @(m_env_cfg.m_straps_vif.strap_en or m_env_cfg.under_reset) begin
        item = new();
        // Sample the strap data and valid
        `uvm_info(`gfn, "Send the strap data and valid zero values after reset.", UVM_HIGH)

        //Wait for the reset to be de-asserted
        wait(!m_env_cfg.under_reset);
        // Get the gpio data in
        item.cio_gpio_i = m_env_cfg.gpio_vif.pins;
        // Wait for one clock cycle to update the registers
        m_env_cfg.clk_rst_vif.wait_clks(2);

        item.strap_en_i = m_env_cfg.m_straps_vif.strap_en;

        if(m_env_cfg.m_straps_vif.strap_en) begin
          item.sampled_straps_o.data  = m_env_cfg.m_straps_vif.tb_port.sampled_straps.data;
          item.sampled_straps_o.valid = m_env_cfg.m_straps_vif.tb_port.sampled_straps.valid;
        end else begin
          item.sampled_straps_o.data  = 0;
          item.sampled_straps_o.valid = 0;
        end
        // Send the sampled straps to the gpio scoreboard.
        mon_ap.write(item);
      end
    end
  endtask
endclass : gpio_strap_monitor
