// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I2C Agent sequence which behaves as an I2C TARGET.
//
// - Receives seq_items from req_analysis_fifo which are sent onto the driver.
// - If the item is requesting to drive an ACK, 50/50 to change this to a NACK instead.
//
class i2c_target_may_nack_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_target_may_nack_seq)
  `uvm_object_new

  virtual task body();
    case (cfg.if_mode)
      Device: send_device_mode_txn();
      Host:    `uvm_fatal(`gfn, "This sequence is for the agent in TARGET-Mode only!")
      default: `uvm_fatal(`gfn, "Invalid cfg.if_mode!")
    endcase
  endtask : body

  virtual task send_device_mode_txn();
    bit [7:0] rdata;
    forever begin
      p_sequencer.req_analysis_fifo.get(req);
      // If it's a read type response, create randomized return data
      if (req.drv_type == RdData) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(rdata)
        req.rdata = rdata;
      end
      // Convert some of the 'DevAck' items from the monitor into NACKs
      if (req.drv_type == DevAck) begin
        if ($urandom_range(0, 1)) begin
          `uvm_info(`gfn, "Converting an ACK to a NACK!", UVM_LOW)
          req.drv_type = DevNack;
        end
      end
      start_item(req);
      finish_item(req);
    end
  endtask

endclass : i2c_target_may_nack_seq
