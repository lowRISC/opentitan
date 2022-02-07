// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_host_driver extends usb20_driver;
  `uvm_component_utils(usb20_host_driver)

  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg

  `uvm_component_new

  bit fs_clk = 0;

  virtual task run_phase(uvm_phase phase);
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

  // reset signals
  virtual task reset_signals();
  endtask

  // generate internal 12MHz clock for driving data on USB lines
  // TODO add configurable variations to frequency up to design defined limits
  task gen_fs_clk();
    forever begin
      fs_clk <= ~fs_clk;
      #((FS_PERIOD_PS / 2) * 1ps);
      fs_clk <= ~fs_clk;
      #((FS_PERIOD_PS / 2) * 1ps);
    end
  endtask : gen_fs_clk

  // Perform NRZI encoding on the stuffed data
  virtual task nrzi_encoding(bit stuffed_data[$],
                                   ref bit nrzi_data[$]);
    nrzi_data[0] = stuffed_data[0];
    for (int i = 1; i < $size(stuffed_data) + 1; i++) begin
      if (stuffed_data[i] == 1) begin
        nrzi_data[i] = ~nrzi_data[i-1];
      end else begin
        nrzi_data[i] = nrzi_data[i-1];
      end;
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)
      // TODO: do the driving part
      if (cfg.drive_diff == 1) begin
        drive_diff();
      end else begin
        drive_single();
      end;
      // send rsp back to seq
      `uvm_info(`gfn, "item sent", UVM_HIGH)
      seq_item_port.item_done(rsp);
    end
  endtask

  // Drive differential USB pins
  task drive_diff();
  //TODO Add driving of interface signals in differential case
  endtask

  // Drive single ended USB line
  task drive_single();
  //TODO Add driving of interface signals in single ended case
  endtask

endclass
