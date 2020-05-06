// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_monitor extends dv_base_monitor #(
    .ITEM_T (i2c_item),
    .CFG_T  (i2c_agent_cfg),
    .COV_T  (i2c_agent_cov)
  );
  `uvm_component_utils(i2c_monitor)

  // analize ports
  uvm_analysis_port #(i2c_item) i2c_analysis_port;

  `uvm_component_new

  i2c_item item;

  function void build_phase(uvm_phase phase);
    i2c_analysis_port = new("i2c_analysis_port", this);
    // reset trans counters
    cfg.vif.num_rd_trans = 0;
    cfg.vif.num_wr_trans = 0;
  endfunction : build_phase

  task run_phase(uvm_phase phase);

    `uvm_info(`gtn, "start collect trans", UVM_DEBUG)
    forever begin
      wait(cfg.vif.mon_rx_cb.rst_ni === 1'b1);
      if (cfg.en_monitor == 1'b1) begin
        phase.raise_objection(this);
        `uvm_info(`gtn, "raise_objection, write starts", UVM_DEBUG)
        // sample host start/restart
        cfg.vif.wait_for_start_repstart_from_host(cfg.thd_sta, cfg.tsu_sta);
        monitor_address(item);
        if (item.addr[0] == 1'b1) monitor_read(item);
        else monitor_write(item);
        i2c_analysis_port.write(item);
        phase.drop_objection(this);
        `uvm_info(`gtn, "drop_objection, write stops", UVM_DEBUG)
      end else begin
        @(cfg.vif.clk_i);
      end
    end
  endtask: run_phase

  virtual task monitor_address(i2c_item item);
    // sample address bit
    for (int i = 1; i < addr_width; i++) begin
      @(cfg.vif.mon_rx_cb.scl_i);
      item.addr[i] = cfg.vif.sda_i;
    end
    // sample r/w bit
    @(cfg.vif.mon_rx_cb.scl_i);
    item.addr[0] = cfg.vif.sda_i; // 1: READ, 0: WRITE
  endtask : monitor_address

  virtual task monitor_write(i2c_item item);
    // sample host write data
    for (int i = 0; i < data_width; i++) begin
      @(cfg.vif.mon_rx_cb.scl_i);
      item.wr_data[i] = cfg.vif.sda_i;
    end
    // sample device ack
    cfg.vif.wait_for_ack_by_device(cfg.tvd_ack);
    // sample host stop/restart
    cfg.vif.wait_for_stop_or_restart_from_host(cfg.tsu_sta, cfg.tsu_sto);
  endtask : monitor_write

  virtual task monitor_read(i2c_item item);
    // sample host read data
    for (int i = 0; i < data_width; i++) begin
      @(cfg.vif.scl_o)
      item.rd_data[i] = cfg.vif.sda_o;
    end
    // sample host ack
    cfg.vif.wait_for_ack_from_host(cfg.tvd_ack);
    // sample stop/restart
    cfg.vif.wait_for_stop_or_restart_from_host(cfg.tsu_sta, cfg.tsu_sto);
  endtask : monitor_read
endclass : i2c_monitor
