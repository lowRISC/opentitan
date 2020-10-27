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
  uvm_analysis_port #(pattgen_item) item_port[NUM_PATTGEN_CHANNELS];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
      item_port[i] = new($sformatf("item_port[%0d]", i), this);
    end
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    wait(cfg.vif.rst_ni);
    collect_trans(phase);
  endtask : run_phase

  virtual protected task collect_trans(uvm_phase phase);
    for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
      fork
        automatic uint channel = i;
        collect_channel_trans(channel);
        reset_thread();
      join_none
    end
  endtask : collect_trans

  virtual protected task collect_channel_trans(uint channel);
    bit  bit_data;
    uint bit_cnt;

    pattgen_item dut_item;
    forever begin
      dut_item = pattgen_item::type_id::create("dut_item");
      bit_cnt = 0;
      fork 
        begin : isolation_thread
          fork
            begin
              do begin
                get_pattgen_bit(channel, cfg.polarity[channel], bit_data);
                dut_item.data_q.push_back(bit_data);
                bit_cnt++;
                `uvm_info(`gfn, $sformatf("\n--> monitor: channel %0d, polar %0b, data[%0d] %b",
                    channel, cfg.polarity[channel], bit_cnt, bit_data), UVM_DEBUG)
              end while (bit_cnt < cfg.length[channel]);
              // avoid race condition (counter is achieved and reset is issued at the same time)
              if (!cfg.reset_asserted) begin
                item_port[channel].write(dut_item);
                `uvm_info(`gfn, $sformatf("\n--> monitor: send dut_item on channel %0d to scb\n%s",
                    channel, dut_item.sprint()), UVM_DEBUG)
              end
            end
            @(posedge cfg.reset_asserted);
          join_any
          disable fork;
        end : isolation_thread
      join
    end
  endtask : collect_channel_trans

  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_ni);
      cfg.reset_asserted = 1'b1;
      // implement other clean-up actions under reset here
      @(posedge cfg.vif.rst_ni);
      cfg.reset_asserted = 1'b0;
    end
  endtask : reset_thread

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.pcl_tx, cfg.vif.pda_tx);
      ok_to_end = (cfg.vif.pcl_tx === {NUM_PATTGEN_CHANNELS{1'b0}}) &&
                  (cfg.vif.pda_tx === {NUM_PATTGEN_CHANNELS{1'b0}});
    end
  endtask : monitor_ready_to_end

  virtual task get_pattgen_bit(uint channel, bit polarity, output bit bit_o);
    `DV_CHECK_LT_FATAL(channel, NUM_PATTGEN_CHANNELS, "invalid channel index")
    if (polarity) begin
      @(negedge cfg.vif.pcl_tx[channel]);
    end else begin
      @(posedge cfg.vif.pcl_tx[channel]);
    end
    bit_o = cfg.vif.pda_tx[channel];
  endtask : get_pattgen_bit

endclass : pattgen_monitor
