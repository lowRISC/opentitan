// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_monitor extends dv_base_monitor #(
    .ITEM_T (i2c_item),
    .CFG_T  (i2c_agent_cfg),
    .COV_T  (i2c_agent_cov)
  );
  `uvm_component_utils(i2c_monitor)

  uvm_analysis_port #(i2c_item) mon_item_port;  // used to send partial rd/wr_tran to driver
  uvm_analysis_port #(i2c_item) wr_item_port;   // used to send complete wr_tran to sb
  uvm_analysis_port #(i2c_item) rd_item_port;   // used to send complete rd_tran to sb

  local i2c_item  mon_dut_item;
  local bit [7:0] mon_data;
  local uint      num_dut_tran = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon_item_port = new("mon_item_port", this);
    wr_item_port  = new("wr_item_port", this);
    rd_item_port  = new("rd_item_port", this);
    mon_dut_item  = i2c_item::type_id::create("mon_dut_item", this);
  endfunction : build_phase

  virtual task wait_for_reset_and_drop_item();
    @(negedge cfg.vif.rst_ni);
    num_dut_tran = 0;
    mon_dut_item.clear_all();
  endtask : wait_for_reset_and_drop_item

  virtual task run_phase(uvm_phase phase);
    wait(cfg.vif.rst_ni);
    forever begin
      fork
        begin: iso_fork
          fork
            begin
              collect_thread(phase);
            end
            begin // if (on-the-fly) reset is monitored, drop the item
              wait_for_reset_and_drop_item();
              `uvm_info(`gfn, $sformatf("\nmonitor is reset, drop item\n%s",
                  mon_dut_item.sprint()), UVM_DEBUG)
            end
          join_any
          disable fork;
        end: iso_fork
      join
    end
  endtask : run_phase

  // collect transactions forever
  virtual protected task collect_thread(uvm_phase phase);
    i2c_item complete_item;

    wait(cfg.en_monitor);
    if (mon_dut_item.stop ||
       (!mon_dut_item.stop && !mon_dut_item.start && !mon_dut_item.rstart)) begin
      cfg.vif.wait_for_host_start(cfg.timing_cfg);
      `uvm_info(`gfn, "\nmonitor, detect HOST START", UVM_DEBUG)
    end else begin
      mon_dut_item.rstart = 1'b1;
    end
    num_dut_tran++;
    mon_dut_item.start = 1'b1;
    // monitor address for non-chained reads
    address_thread();
    // monitor read/write data
    if (mon_dut_item.bus_op == BusOpRead) read_thread();
    else                                  write_thread();
    // send rsp_item to scoreboard
    `downcast(complete_item, mon_dut_item.clone());
    complete_item.stop = 1'b1;
    if (cfg.vif.rst_ni && complete_item.stop && complete_item.start) begin
      if (complete_item.bus_op == BusOpRead) rd_item_port.write(complete_item);
      else                                   wr_item_port.write(complete_item);
      `uvm_info(`gfn, $sformatf("\nmonitor, send complete item to scb\n%s",
          complete_item.sprint()), UVM_DEBUG)
    end
    mon_dut_item.clear_data();
  endtask: collect_thread

  virtual protected task address_thread();
    i2c_item clone_item;
    bit rw_req = 1'b0;

    // sample address and r/w bit
    mon_dut_item.tran_id = num_dut_tran;
    for (int i = cfg.target_addr_mode - 1; i >= 0; i--) begin
      cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_dut_item.addr[i]);
    `uvm_info(`gfn, $sformatf("\nmonitor, address[%0d] %b", i, mon_dut_item.addr[i]), UVM_DEBUG)
    end
    cfg.vif.get_bit_data("host", cfg.timing_cfg, rw_req);
    mon_dut_item.bus_op = (rw_req) ? BusOpRead : BusOpWrite;
    // get ack after transmitting address
    mon_dut_item.drv_type = DevAck;
    `downcast(clone_item, mon_dut_item.clone());
    mon_item_port.write(clone_item);
    cfg.vif.wait_for_device_ack(cfg.timing_cfg);
    `uvm_info(`gfn, $sformatf("\nmonitor, address, detect TARGET ACK"), UVM_DEBUG)
  endtask : address_thread

  virtual protected task read_thread();
    i2c_item clone_item;
    
    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    mon_dut_item.ack    = 1'b0;
    mon_dut_item.nack   = 1'b0;
    while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
      // ask driver response read data
      mon_dut_item.drv_type = RdData;
      `downcast(clone_item, mon_dut_item.clone());
      mon_item_port.write(clone_item);
      // sample read data
      for (int i = 7; i >= 0; i--) begin
        cfg.vif.get_bit_data("device", cfg.timing_cfg, mon_data[i]);
        `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, trans %0d, byte %0d, bit[%0d] %0b",
            mon_dut_item.tran_id, mon_dut_item.num_data+1, i, mon_data[i]), UVM_DEBUG)
      end
      mon_dut_item.data_q.push_back(mon_data);
      mon_dut_item.num_data++;
      `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, trans %0d, byte %0d 0x%0x",
          mon_dut_item.tran_id, mon_dut_item.num_data, mon_data), UVM_DEBUG)
      // sample host ack/nack (in the last byte, nack can be issue if rcont is set)
      cfg.vif.wait_for_host_ack_or_nack(cfg.timing_cfg, mon_dut_item.ack, mon_dut_item.nack);
      `DV_CHECK_NE_FATAL({mon_dut_item.ack, mon_dut_item.nack}, 2'b11)
      `uvm_info(`gfn, $sformatf("\nmonitor, detect HOST %s",
          (mon_dut_item.ack) ? "ACK" : "NO_ACK"), UVM_DEBUG)
      // if nack is issued, next bit must be stop or rstart
      if (mon_dut_item.nack) begin
        cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                             mon_dut_item.rstart,
                                             mon_dut_item.stop);
        `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
        `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, detect HOST %s",
            (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_DEBUG)
      end
    end
  endtask : read_thread

  virtual protected task write_thread();
    i2c_item clone_item;

    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
      fork
        begin : iso_fork_write
          fork
            begin
              // ask driver's response a write request
              mon_dut_item.drv_type = WrData;
              `downcast(clone_item, mon_dut_item.clone());
              mon_item_port.write(clone_item);
              for (int i = 7; i >= 0; i--) begin
                cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_data[i]);
              end
              mon_dut_item.num_data++;
              mon_dut_item.data_q.push_back(mon_data);
              mon_dut_item.drv_type = DevAck;
              `downcast(clone_item, mon_dut_item.clone());
              mon_item_port.write(clone_item);
              cfg.vif.wait_for_device_ack(cfg.timing_cfg);
            end
            begin
              cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                   mon_dut_item.rstart,
                                                   mon_dut_item.stop);
              `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
              `uvm_info(`gfn, $sformatf("\nmonitor, wr_data, detect HOST %s %0b",
                  (mon_dut_item.stop) ? "STOP" : "RSTART", mon_dut_item.stop), UVM_DEBUG)
            end
          join_any
          disable fork;
        end : iso_fork_write
      join
    end
  endtask : write_thread

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.scl_i or cfg.vif.sda_i or cfg.vif.scl_o or cfg.vif.sda_o);
      ok_to_end = (cfg.vif.scl_i == 1'b1) && (cfg.vif.sda_i == 1'b1);
    end
  endtask : monitor_ready_to_end

endclass : i2c_monitor

