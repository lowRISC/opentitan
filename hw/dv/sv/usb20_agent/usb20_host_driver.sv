// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_host_driver extends usb20_driver;
  `uvm_component_utils(usb20_host_driver)

  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg

  `uvm_component_new

  // reset signals
  virtual task reset_signals();
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
