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
    @(negedge vif.host_driver_cb.reset);
    forever begin
      vif.wait_clks(1);
      seq_item_port.get_next_item(req);
      vif.wait_clks(req.req_delay);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      drive_transfer(rsp);
      seq_item_port.item_done();
    end
  endtask : get_and_drive

  virtual protected task reset_signals();
    forever begin
      @(posedge vif.host_driver_cb.reset);
      vif.host_driver_cb.request        <= 'h0;
      vif.host_driver_cb.addr           <= 'hz;
      vif.host_driver_cb.wdata          <= 'hz;
      vif.host_driver_cb.be             <= 'bz;
      vif.host_driver_cb.we             <= 'bz;
    end
  endtask : reset_signals

  virtual protected task drive_transfer (ibex_mem_intf_seq_item trans);
    if (trans.req_delay > 0) begin
      vif.wait_clks(trans.req_delay);
    end
    vif.host_driver_cb.request <= 1'b1;
    vif.host_driver_cb.addr    <= trans.addr;
    vif.host_driver_cb.be      <= trans.be;
    vif.host_driver_cb.we      <= trans.read_write;
    vif.host_driver_cb.wdata   <= trans.data;
    wait (vif.host_driver_cb.grant === 1'b1);
    vif.wait_clks(1);
    vif.host_driver_cb.request <= 'h0;
    vif.host_driver_cb.addr    <= 'hz;
    vif.host_driver_cb.wdata   <= 'hz;
    vif.host_driver_cb.be      <= 'bz;
    vif.host_driver_cb.we      <= 'bz;
    rdata_queue.put(trans);
  endtask : drive_transfer

  virtual protected task collect_response();
    ibex_mem_intf_seq_item tr;
    forever begin
      rdata_queue.get(tr);
      vif.wait_clks(1);
      while(vif.rvalid !== 1'b1) vif.wait_clks(1);
      if(tr.read_write == READ)
        tr.data = vif.host_driver_cb.rdata;
      seq_item_port.put_response(tr);
    end
  endtask : collect_response

endclass : ibex_mem_intf_master_driver
