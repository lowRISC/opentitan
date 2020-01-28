// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_monitor extends dv_base_monitor #(
    .ITEM_T (i2c_item),
    .CFG_T  (i2c_agent_cfg),
    .COV_T  (i2c_agent_cov)
  );
  `uvm_component_utils(i2c_monitor)

  // the base class provides the following handles for use:
  i2c_agent_cfg       cfg;
  i2c_agent_cov       cov;
  i2c_common_tasks    common_tasks;

  event start_detection_e;
  event stop_detection_e;

  int trans_index = 0;

  // analize ports
  uvm_analysis_port #(i2c_item) rx_analysis_port;
  uvm_analysis_port #(i2c_item) tx_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rx_analysis_port = new("rx_analysis_port", this);
    tx_analysis_port = new("tx_analysis_port", this);

    common_tasks = i2c_common_tasks::type_id::create("common_tasks", this);
    common_tasks.vif = cfg.vif;

    // reset trans counters
    cfg.vif.num_rd_trans = 0;
    cfg.vif.num_wr_trans = 0;
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    `uvm_info(`gtn, "start collect trans", UVM_DEBUG)
    fork
      collect_tx_trans(phase);
      collect_rx_trans(phase);
    join
  endtask: run_phase

  virtual task collect_tx_trans(uvm_phase phase);
    i2c_item item;

    `uvm_info(`gtn, $sformatf("monitor en_tx_monitor: %b", cfg.en_tx_monitor), UVM_LOW)
    `uvm_info(`gtn, $sformatf("monitor en_tx_checks:  %b", cfg.en_tx_checks), UVM_LOW)

    //forever common_tasks.monitor_for_start_condition( .start_e(start_detection_e) );
    //forever common_tasks.monitor_for_stop_condition(  .stop_e(stop_detection_e) );

    forever begin
      wait(cfg.vif.mon_rx_cb.rst_ni === 1'b1);

      if (cfg.en_tx_monitor == 1'b1) begin
        `uvm_info(`gtn, "raise_objection, TX starts", UVM_DEBUG)
        phase.raise_objection(this);

        // detect START
        common_tasks.wait_for_start_by_host();
        if (cfg.en_tx_checks && cfg.vif.status !== "START") `uvm_error(`gtn, "START failed")

        // detect R/W bit
        @(posedge cfg.vif.mon_rx_cb.scl_i);
        item.addr[0] = cfg.vif.sda_i; // 1: READ, 0: WRITE
        cfg.vif.rw_dir = "WR";
        if (cfg.en_tx_checks && cfg.vif.status !== "WR") `uvm_error(`gtn, "WRITE failed")

        // detect ADDRESS bit
        for(int i = 1; i < `I2C_ADDR_WIDTH; i++) begin
          @(posedge cfg.vif.mon_rx_cb.scl_i);
          item.addr[i] = cfg.vif.sda_i;
          cfg.vif.status = "WR_ADDR";
        end
        if (cfg.en_tx_checks &&cfg.vif.status !== "WR_ADDR") `uvm_error(`gtn, "WR_ADDR failed")

        // host WRITE
        for (int i = 0; i < `I2C_DATA_WIDTH; i++) begin
          if (cfg.vif.mon_rx_cb.scl_i === 1'b1) begin
            item.wr_data[i] = cfg.vif.sda_i;
            cfg.vif.status = "WR_DATA";
          end
          if (cfg.en_tx_checks && cfg.vif.status !== "WR_DATA") `uvm_error(`gtn, "WR_DATA failed")
        end

        // detect DEV_ACK bit
        common_tasks.wait_for_ack_by_dev();
        if (cfg.en_tx_checks && cfg.vif.status !== "DEV_ACK") `uvm_error(`gtn, "DEV_ACK failed")

        // detect STOP/REP_START bit
        fork
          common_tasks.wait_for_stop_by_host();
          common_tasks.wait_for_repstart_by_host();
        join_any
        if ( cfg.en_tx_checks &&
             (cfg.vif.status !== "STOP" || cfg.vif.status !== "REP_START"))
          `uvm_error(`gtn, "STOP/REP_START failed")

        cfg.vif.num_wr_trans++;
        `uvm_info(`gtn, $sformatf("collected i2c tx trans %d:\n%0s",
                        cfg.vif.num_wr_trans, item.sprint()), UVM_DEBUG)
        tx_analysis_port.write(item);

        phase.drop_objection(this);
        `uvm_info(`gtn, "drop_objection, TX starts", UVM_DEBUG)
      end else begin
        @(cfg.vif.clk_i);
      end
    end
  endtask : collect_tx_trans

  virtual task collect_rx_trans(uvm_phase phase);
    i2c_item item;
    bit      nack = 1'b0;

    `uvm_info(`gtn, $sformatf("monitor en_rx_monitor: %b", cfg.en_rx_monitor), UVM_LOW)
    `uvm_info(`gtn, $sformatf("monitor en_rx_checks:  %b", cfg.en_rx_checks), UVM_LOW)

    forever begin
      wait(cfg.vif.mon_rx_cb.rst_ni === 1'b1);

      if (cfg.en_rx_monitor == 1) begin
        phase.raise_objection(this);
        `uvm_info(`gtn, "raise_objection, RX starts", UVM_DEBUG)
        item = i2c_item::type_id::create("item");

        // detect START
        common_tasks.wait_for_start_by_host();
        if (cfg.en_rx_checks && cfg.vif.status !== "START") `uvm_error(`gtn, "START failed")

        // detect R/W bit
        @(posedge cfg.vif.mon_rx_cb.scl_i);
        item.addr[0] = cfg.vif.sda_i; // 1: READ, 0: WRITE
        cfg.vif.rw_dir = "RD";
        if (cfg.en_rx_checks && cfg.vif.status !== "RD") `uvm_error(`gtn, "READ failed")

        // detect ADDRESS bit
        for(int i = 1; i < `I2C_ADDR_WIDTH; i++) begin
          @(posedge cfg.vif.mon_rx_cb.scl_i);
          item.addr[i] = cfg.vif.sda_i;
          cfg.vif.status = "RD_ADDR";
        end
        if (cfg.en_rx_checks && cfg.vif.status !== "RD_ADDR") `uvm_error(`gtn, "RD_ADDR failed")

        // host READ
        if (cfg.vif.rw_dir === "RD") begin
          for (int i = 0; i < `I2C_DATA_WIDTH; i++) begin
            @(posedge cfg.vif.clk_i);
            if (cfg.vif.mon_tx_cb.scl_o === 1'b1) begin
              item.rd_data[i] <= cfg.vif.sda_o;
              cfg.vif.status = "RD_DATA";
            end
            if (cfg.en_rx_checks && cfg.vif.status !== "RD_DATA")
              `uvm_error(`gtn, "RD_DATA failed")
          end

          fork
            common_tasks.wait_for_ack_by_host();
            common_tasks.wait_for_nack_by_host(.nack(nack));
          join_any

          if (cfg.en_rx_checks) begin
            if (nack)
              if (cfg.vif.status !== "HST_NACK") `uvm_error(`gtn, "HST_NACK failed")
            else
              if (cfg.vif.status !== "HST_ACK") `uvm_error(`gtn, "HST_ACK failed")

            common_tasks.wait_for_stop_by_host();
            if (cfg.en_rx_checks && cfg.vif.status !== "STOP") `uvm_error(`gtn, "STOP failed")
          end
        end

        cfg.vif.num_rd_trans++;
        `uvm_info(`gtn, $sformatf("collected i2c rx trans %d:\n%0s",
            cfg.vif.num_rd_trans, item.sprint()), UVM_DEBUG)
        rx_analysis_port.write(item);

        phase.drop_objection(this);
        `uvm_info(`gtn, "drop_objection, RX starts", UVM_DEBUG)
      end else begin
        @(cfg.vif.clk_i);
      end
    end
  endtask : collect_rx_trans

endclass : i2c_monitor
