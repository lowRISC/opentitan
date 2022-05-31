// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_monitor
//------------------------------------------------------------------------------

class ibex_mem_intf_monitor extends uvm_monitor;

  protected virtual ibex_mem_intf vif;

  mailbox #(ibex_mem_intf_seq_item)          collect_response_queue;
  uvm_analysis_port#(ibex_mem_intf_seq_item) item_collected_port;
  uvm_analysis_port#(ibex_mem_intf_seq_item) addr_ph_port;

  `uvm_component_utils(ibex_mem_intf_monitor)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    item_collected_port = new("item_collected_port", this);
    addr_ph_port = new("addr_ph_port_monitor", this);
    collect_response_queue = new();
    if(!uvm_config_db#(virtual ibex_mem_intf)::get(this, "", "vif", vif)) begin
       `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
    end
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    wait (vif.monitor_cb.reset === 1'b0);
    forever begin
      fork : check_mem_intf
        collect_address_phase();
        collect_response_phase();
        wait (vif.monitor_cb.reset === 1'b1);
      join_any
      // Will only reach this point when mid-test reset is asserted
      disable fork;
      handle_reset();
    end
  endtask : run_phase

  virtual protected task handle_reset();
    ibex_mem_intf_seq_item mailbox_result;
    // Clear the mailbox of any content
    while (collect_response_queue.try_get(mailbox_result));
    wait (vif.monitor_cb.reset === 1'b0);
  endtask

  virtual protected task collect_address_phase();
    ibex_mem_intf_seq_item trans_collected;
    forever begin
      trans_collected = ibex_mem_intf_seq_item::type_id::create("trans_collected");
      while(!(vif.monitor_cb.request && vif.monitor_cb.grant)) vif.wait_clks(1);
      trans_collected.addr              = vif.monitor_cb.addr;
      trans_collected.be                = vif.monitor_cb.be;
      trans_collected.misaligned_first  = vif.monitor_cb.misaligned_first;
      trans_collected.misaligned_second = vif.monitor_cb.misaligned_second;
      `uvm_info(get_full_name(), $sformatf("Detect request with address: %0x",
                trans_collected.addr), UVM_HIGH)
      if(vif.monitor_cb.we) begin
        trans_collected.read_write = WRITE;
        trans_collected.data = vif.monitor_cb.wdata;
        trans_collected.intg = vif.monitor_cb.wintg;
      end else begin
        trans_collected.read_write = READ;
      end
      addr_ph_port.write(trans_collected);
      `uvm_info(get_full_name(),"Send through addr_ph_port", UVM_HIGH)
      collect_response_queue.put(trans_collected);
      vif.wait_clks(1);
    end
  endtask : collect_address_phase

  virtual protected task collect_response_phase();
    ibex_mem_intf_seq_item trans_collected;
    forever begin
      collect_response_queue.get(trans_collected);
      do
        vif.wait_clks(1);
      while(vif.monitor_cb.rvalid === 0);

      if (trans_collected.read_write == READ) begin
        trans_collected.data = vif.monitor_cb.rdata;
        trans_collected.intg = vif.monitor_cb.rintg;
      end

      trans_collected.error = vif.monitor_cb.error;
      item_collected_port.write(trans_collected);
    end
  endtask : collect_response_phase

endclass : ibex_mem_intf_monitor
