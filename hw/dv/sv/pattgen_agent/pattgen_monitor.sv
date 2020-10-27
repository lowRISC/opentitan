// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_monitor extends dv_base_monitor #(
    .ITEM_T (pattgen_item),
    .CFG_T  (pattgen_agent_cfg),
    .COV_T  (pattgen_agent_cov)
  );
  `uvm_component_utils(pattgen_monitor)
  `uvm_component_new

  // analysis ports connected to scb
  uvm_analysis_port #(pattgen_item) ch0_item_port;   // used to send items on ch0 to scb
  uvm_analysis_port #(pattgen_item) ch1_item_port;   // used to send items on ch1 to scb

  local pattgen_item ch0_dut_item;
  local pattgen_item ch1_dut_item;

  // counters for generated bits on channels
  uint cnt_ch0 = 0;
  uint cnt_ch1 = 0;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ch0_item_port = new("ch0_item_port", this);
    ch1_item_port = new("ch1_item_port", this);
    ch0_dut_item  = new("ch0_dut_item");
    ch1_dut_item  = new("ch1_dut_item");
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    wait(cfg.vif.rst_ni);
    collect_trans(phase);
  endtask : run_phase
  
  // collect items forever
  virtual protected task collect_trans(uvm_phase phase);
    pattgen_item ch0_item, ch1_item;

    forever begin
      wait(cfg.en_monitor);
      fork
        begin // collect items on the channel 0
          cfg.vif.get_bit(.channel("Channel0"), .polarity(cfg.polarity_ch0),
                          .bit_o(ch0_dut_item.data));
          `downcast(ch0_item, ch0_dut_item.clone());
          ch0_item_port.write(ch0_item);
        end
        begin // collect items on the channel 1
          cfg.vif.get_bit(.channel("Channel1"), .polarity(cfg.polarity_ch1),
                          .bit_o(ch1_dut_item.data));
          `downcast(ch1_item, ch1_dut_item.clone());
          ch1_item_port.write(ch1_item);
        end
        begin // if (on-the-fly) reset is monitored, drop the item
          @(negedge cfg.vif.rst_ni);
          `uvm_info(`gfn, $sformatf("\nmonitor is reset, drop item on channel 0\n%s",
              ch0_dut_item.sprint()), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("\nmonitor is reset, drop item on channel 1\n%s",
              ch1_dut_item.sprint()), UVM_DEBUG)
        end
      join_any
      disable fork;
    end
  endtask : collect_trans

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.pcl0_tx or cfg.vif.pda0_tx or cfg.vif.pcl1_tx or cfg.vif.pda1_tx);
      ok_to_end = (cfg.vif.pcl0_tx == 1'b0) && (cfg.vif.pda0_tx == 1'b0) &&
                  (cfg.vif.pcl1_tx == 1'b0) && (cfg.vif.pda1_tx == 1'b0);
    end
  endtask : monitor_ready_to_end

endclass : pattgen_monitor
