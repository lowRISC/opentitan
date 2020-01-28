// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_driver extends i2c_driver;
  `uvm_component_utils(i2c_device_driver)

  bit [data_width-1:0] data_byte;
  bit [addr_width-1:0] addr_byte;
  bit rw_dir;

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    get_and_drive();
  endtask : run_phase

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get(req);     // get req handler with type i2c_item
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("i2c gets next item:\n%0s", req.sprint()), UVM_DEBUG)
      // address phase
      process_address();
      // data phase
      if (rw_dir == 1'b1 && cfg.en_monitor == 1'b1)      process_read_data();
      else if (rw_dir == 1'b0 && cfg.en_monitor == 1'b1) process_write_data();
      // send rsp back to seq
      `uvm_info(`gfn, "device item sent", UVM_DEBUG)
      seq_item_port.put_response(rsp);
    end
  endtask : get_and_drive

  task process_address();
    // device waits for START/RESTART on bus
    cfg.vif.wait_for_start_repstart_from_host(cfg.thd_sta, cfg.tsu_sta);
    `uvm_info(`gfn, $sformatf("i2c request type %d (R/W=1/0)", addr_byte[0]), UVM_DEBUG)
    // device gets address bits from host
    for (int i = 1; i < addr_width; i++) begin
      wait(cfg.vif.scl_i == 1'b1);
      addr_byte[i] = cfg.vif.sda_i;
      cfg.vif.bus_status = HostSendAddr;
    end
    // device gets r/w bit from host
    wait(cfg.vif.scl_i == 1'b1);
    addr_byte[0] = cfg.vif.sda_i;
    rw_dir = cfg.vif.sda_i;
    cfg.vif.bus_status = HostSendRWBit;
    rsp.addr = addr_byte;
    rsp.mem_addrs.push_front(addr_byte);
    // device sends ack to host
    cfg.vif.wait_for_dly(req.dly_to_send_ack);
    cfg.vif.send_ack_by_device(cfg.tvd_ack);
  endtask : process_address

  task process_read_data();
    `uvm_info(`gfn, $sformatf("i2c processes read data"), UVM_DEBUG)
    // if mem_datas is empty then return a random read data to response host
    data_byte = (req.mem_datas.size()>0) ? req.mem_datas.pop_back() : gen_rand_rd_data();
    // bit serialization
    for (int i = 0; i < data_width; i++) begin
      cfg.vif.scl_o <= 1'b0;
      // send data bit
      cfg.vif.scl_o <= 1'b0;
      cfg.vif.wait_for_dly(req.dly_to_send_data);
      cfg.vif.scl_o <= 1'b1;
      cfg.vif.sda_o <= data_byte[i];
      cfg.vif.bus_status = HostReceiveData;
      // device must ensure hold time thd_dat when sending read data
      repeat(cfg.thd_dat) @(posedge cfg.vif.clk_i);
    end
    rsp.rd_data = data_byte;
    // wait for nack from host
    cfg.vif.wait_for_nack_from_host(cfg.tvd_ack);
    // wait for stop/restart from host
    cfg.vif.wait_for_stop_or_restart_from_host(cfg.tsu_sta, cfg.tsu_sto);
  endtask : process_read_data

  task process_write_data();
    `uvm_info(`gfn, $sformatf("i2c processes write data"), UVM_DEBUG)
    // bit concatenation
    for (int i = 0; i < data_width; i++) begin
      wait(cfg.vif.scl_i == 1'b1)
      data_byte[i] = cfg.vif.sda_i;
      cfg.vif.bus_status = HostWriteData;
    end
    rsp.wr_data = data_byte;
    rsp.mem_datas.push_front(data_byte);
    // device sends ack to host
    cfg.vif.wait_for_dly(req.dly_to_send_ack);
    cfg.vif.send_ack_by_device(cfg.tvd_ack);
    // wait for stop/restart from host
    cfg.vif.wait_for_dly(req.dly_to_send_stop);
    cfg.vif.wait_for_stop_or_restart_from_host(cfg.tsu_sta, cfg.tsu_sto);
  endtask : process_write_data

  function gen_rand_rd_data();
    return $urandom_range((1 << data_width) - 1, 0);
  endfunction

endclass : i2c_device_driver

