// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A basic reactive agent sequence which drives a controller transaction, and automatically ends
// the transaction with a STOP condition if a target NACK is seen in response to any write-byte.
//
class i2c_controller_base_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_controller_base_seq)
  `uvm_object_new

  virtual task send_controller_txn();

    // Set this bit when the monitor observes a NACK from the target device.
    bit got_nack;

    // Wait until we get stimulus from the vseq.
    wait (req_q.size() > 0);

    fork
      begin
        // Spawn a task that watches for NACK.

        cfg.got_nack.wait_trigger();
        `uvm_info(`gfn, "Monitor triggered the 'got_nack' event!", UVM_MEDIUM)
        got_nack = 1;
      end
      begin
        // Drive the stimulus items, either until all items have been sent or
        // until we see a NACK from the DUT-Target.

        while (req_q.size() > 0 && !got_nack) begin
          req = req_q.pop_front();
          start_item(req);
          finish_item(req);
        end

        if (got_nack) begin
          `uvm_info(`gfn, "Got a NACK, driving a STOP symbol now to end the txn.", UVM_MEDIUM)
          `uvm_create_obj(REQ, req)
          req.drv_type = HostStop;
          start_item(req);
          finish_item(req);
        end
      end
    join

  endtask

  virtual task send_host_mode_txn();
    send_controller_txn();
  endtask

endclass: i2c_controller_base_seq
