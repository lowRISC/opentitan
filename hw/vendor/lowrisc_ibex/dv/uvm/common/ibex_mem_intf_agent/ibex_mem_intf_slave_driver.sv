// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_slave_driver
//------------------------------------------------------------------------------

class ibex_mem_intf_slave_driver extends uvm_driver #(ibex_mem_intf_seq_item);

  protected virtual ibex_mem_intf vif;

  `uvm_component_utils(ibex_mem_intf_slave_driver)
  `uvm_component_new

  mailbox #(ibex_mem_intf_seq_item) grant_queue;
  mailbox #(ibex_mem_intf_seq_item) rdata_queue;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    grant_queue = new();
    rdata_queue = new();
    if(!uvm_config_db#(virtual ibex_mem_intf)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    reset_signals();
    fork
      send_grant();
    join_none
    get_and_drive();
  endtask : run_phase

  virtual protected task reset_signals();
    vif.rvalid  <= 1'b0;
    vif.grant   <= 1'b0;
    vif.rdata   <= 'b0;
  endtask : reset_signals

  virtual protected task get_and_drive();
    @(negedge vif.reset);
    fork
      forever begin
        ibex_mem_intf_seq_item req, req_c;
        @(posedge vif.clock);
        seq_item_port.get_next_item(req);
        $cast(req_c, req.clone());
        if(~vif.reset) begin
          rdata_queue.put(req_c);
        end
        seq_item_port.item_done();
      end
      send_read_data();
    join_none
  endtask : get_and_drive

  // TODO(udinator) - this direct send_grant logic is temporary until instruction fetch protocol
  // issue is clarified (https://github.com/lowRISC/ibex/pull/293). After resolution, will re-add
  // random delays insertion before driving grant to the ibex core.
  virtual protected task send_grant();
    int gnt_delay;
    forever begin
      while(vif.request !== 1'b1) begin
        @(negedge vif.clock);
      end
      if(~vif.reset) begin
        vif.grant = 1'b1;
        @(negedge vif.clock);
        vif.grant = 1'b0;
      end
    end
  endtask : send_grant

  virtual protected task send_read_data();
    ibex_mem_intf_seq_item tr;
    forever begin
      @(posedge vif.clock);
      vif.rvalid <=  1'b0;
      vif.rdata  <= 'x;
      rdata_queue.get(tr);
      if(vif.reset) continue;
      repeat(tr.rvalid_delay) @(posedge vif.clock);
      if(~vif.reset) begin
        vif.rvalid <=  1'b1;
        vif.rdata  <=  tr.data;
      end
    end
  endtask : send_read_data

endclass : ibex_mem_intf_slave_driver
