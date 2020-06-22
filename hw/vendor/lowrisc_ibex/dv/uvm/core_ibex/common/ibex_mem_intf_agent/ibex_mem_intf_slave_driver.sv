// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_slave_driver
//------------------------------------------------------------------------------

class ibex_mem_intf_slave_driver extends uvm_driver #(ibex_mem_intf_seq_item);

  protected virtual ibex_mem_intf vif;

  int unsigned min_grant_delay = 0;
  int unsigned max_grant_delay = 10;

  `uvm_component_utils(ibex_mem_intf_slave_driver)
  `uvm_component_new

  mailbox #(ibex_mem_intf_seq_item) rdata_queue;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rdata_queue = new();
    if(!uvm_config_db#(virtual ibex_mem_intf)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    reset_signals();
    wait (vif.device_driver_cb.reset === 1'b0);
    forever begin
      fork : drive_stimulus
        send_grant();
        get_and_drive();
        wait (vif.device_driver_cb.reset === 1'b1);
      join_any
      // Will only be reached after mid-test reset
      disable drive_stimulus;
      handle_reset();
    end
  endtask : run_phase

  virtual protected task handle_reset();
    ibex_mem_intf_seq_item req;
    // Clear mailbox
    while (rdata_queue.try_get(req));
    // Clear seq_item_port
    do begin
      seq_item_port.try_next_item(req);
      if (req != null) begin
        seq_item_port.item_done();
      end
    end while (req != null);
    reset_signals();
    wait (vif.device_driver_cb.reset === 1'b0);
  endtask

  virtual protected task reset_signals();
    vif.device_driver_cb.rvalid  <= 1'b0;
    vif.device_driver_cb.grant   <= 1'b0;
    vif.device_driver_cb.rdata   <= 'b0;
    vif.device_driver_cb.error   <= 1'b0;
  endtask : reset_signals

  virtual protected task get_and_drive();
    wait (vif.device_driver_cb.reset === 1'b0);
    fork
      begin
        forever begin
          ibex_mem_intf_seq_item req, req_c;
          vif.wait_clks(1);
          seq_item_port.get_next_item(req);
          $cast(req_c, req.clone());
          if(~vif.device_driver_cb.reset) begin
            rdata_queue.put(req_c);
          end
          seq_item_port.item_done();
        end
      end
      begin
        send_read_data();
      end
    join
  endtask : get_and_drive

  virtual protected task send_grant();
    int gnt_delay;
    forever begin
      while(vif.device_driver_cb.request !== 1'b1) begin
        vif.wait_neg_clks(1);
      end
      if (!std::randomize(gnt_delay) with {
        gnt_delay dist {
          min_grant_delay                         :/ 1,
          [min_grant_delay+1 : max_grant_delay-1] :/ 1,
          max_grant_delay                         :/ 1
        };
      }) begin
        `uvm_fatal(`gfn, $sformatf("Cannot randomize grant"))
      end
      vif.wait_neg_clks(gnt_delay);
      if(~vif.device_driver_cb.reset) begin
        vif.device_driver_cb.grant <= 1'b1;
        vif.wait_neg_clks(1);
        vif.device_driver_cb.grant <= 1'b0;
      end
    end
  endtask : send_grant

  virtual protected task send_read_data();
    ibex_mem_intf_seq_item tr;
    forever begin
      vif.wait_clks(1);
      vif.device_driver_cb.rvalid <=  1'b0;
      vif.device_driver_cb.rdata  <= 'x;
      vif.device_driver_cb.error  <= 1'b0;
      rdata_queue.get(tr);
      if(vif.device_driver_cb.reset) continue;
      vif.wait_clks(tr.rvalid_delay);
      if(~vif.device_driver_cb.reset) begin
        vif.device_driver_cb.rvalid <=  1'b1;
        vif.device_driver_cb.error  <=  tr.error;
        vif.device_driver_cb.rdata  <=  tr.data;
      end
    end
  endtask : send_read_data

endclass : ibex_mem_intf_slave_driver
