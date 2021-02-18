// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_device_driver extends csrng_driver;
  `uvm_component_utils(csrng_device_driver)
  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // TODO: drive_trans
  // reset signals
  virtual task reset_signals();
    if (cfg.if_mode == Device) begin
      cfg.vif.req_push_if.ready_int <= '0;
      cfg.vif.genbits_push_if.valid_int <= '0;
    end
//    end else begin
//      cfg.vif.ack_int   <= '0;
//    end
//    cfg.vif.d_data_int <= 'x;
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      // TODO: do the driving part
      //
      // send rsp back to seq
      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

endclass
