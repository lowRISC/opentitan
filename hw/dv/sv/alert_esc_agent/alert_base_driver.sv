// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Virtual base class used for alert_sender_driver and alert_receiver_driver

virtual class alert_base_driver extends alert_esc_base_driver;
  // Items that have been taken from seq_item_port and should be sent
  protected uvm_tlm_analysis_fifo #(alert_seq_item) m_requests;

  extern function new (string name, uvm_component parent);

  // Take items from the sequencer and drive them. This implements a task from dv_base_driver.
  extern virtual task get_and_drive();

  // Monitor seq_item_port and add the items to the various queues
  //
  // This is run by get_and_drive.
  extern local task get_req();

  // Drive items that have been added to the various queues by get_req
  //
  // This should run forever and is started by get_and_drive.
  pure virtual task drive_req();
endclass

function alert_base_driver::new (string name, uvm_component parent);
  super.new(name, parent);
  m_requests = new("m_requests", this);
endfunction : new

task alert_base_driver::get_and_drive();
  fork
    get_req();
    drive_req();
  join
endtask

task alert_base_driver::get_req();
  wait(!cfg.in_reset);
  forever begin
    alert_seq_item req_clone;
    seq_item_port.get(req);
    `downcast(req_clone, req.clone());
    req_clone.set_id_info(req);
    m_requests.write(req_clone);
    `uvm_info(`gfn,
              $sformatf("Driver received item (after pushing): %0s", req_clone.m_txn_type.name()),
              UVM_DEBUG)
  end
endtask : get_req
