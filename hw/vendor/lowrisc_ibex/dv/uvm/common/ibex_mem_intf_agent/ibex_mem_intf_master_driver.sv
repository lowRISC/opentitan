// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_master_driver
//------------------------------------------------------------------------------

class ibex_mem_intf_master_driver extends uvm_driver #(ibex_mem_intf_seq_item);

  protected virtual ibex_mem_intf vif;

  `uvm_component_utils(ibex_mem_intf_master_driver)
  `uvm_component_new

  mailbox #(ibex_mem_intf_seq_item) rdata_queue;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rdata_queue = new();
    if(!uvm_config_db#(virtual ibex_mem_intf)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
      collect_response();
    join
  endtask : run_phase

  virtual protected task get_and_drive();
    @(negedge vif.reset);
    forever begin
      @(posedge vif.clock);
      seq_item_port.get_next_item(req);
      repeat(req.req_delay) @(posedge vif.clock);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      drive_transfer(rsp);
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  virtual protected task reset_signals();
    forever begin
      @(posedge vif.reset);
      vif.request        <= 'h0;
      vif.addr           <= 'hz;
      vif.wdata          <= 'hz;
      vif.be             <= 'bz;
      vif.we             <= 'bz;
    end
  endtask : reset_signals

  virtual protected task drive_transfer (ibex_mem_intf_seq_item trans);
    if (trans.req_delay > 0) begin
      repeat(trans.req_delay) @(posedge vif.clock);
    end
    vif.request <= 1'b1;
    vif.addr    <= trans.addr;
    vif.be      <= trans.be;
    vif.we      <= trans.read_write;
    vif.wdata   <= trans.data;
    wait(vif.grant === 1'b1);
    @(posedge vif.clock);
    vif.request <= 'h0;
    vif.addr    <= 'hz;
    vif.wdata   <= 'hz;
    vif.be      <= 'bz;
    vif.we      <= 'bz;
    rdata_queue.put(trans);
  endtask : drive_transfer

  virtual protected task collect_response();
    ibex_mem_intf_seq_item tr;
    forever begin
      rdata_queue.get(tr);
      @(posedge vif.clock);
      while(vif.rvalid !== 1'b1) @(posedge vif.clock);
      if(tr.read_write == READ)
        tr.data = vif.rdata;
      seq_item_port.put_response(tr);
    end
  endtask : collect_response

endclass : ibex_mem_intf_master_driver
