// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I2C Agent sequence which behaves as an I2C TARGET.
//
// - Uses the base-class hooks which determine that state of an inprogress transfer.
// - Each time the I2C-Target is required to ACK/NACk during a transfer, this sequence randomly
//   selects betwee an ACK or NACK.
//
class i2c_target_may_nack_seq extends i2c_base_seq;

  ///////////////
  // VARIABLES //
  ///////////////

  i2c_pkg::acknack_e acknack;

  `uvm_object_utils(i2c_target_may_nack_seq)
  `uvm_object_new

  /////////////
  // METHODS //
  /////////////


  virtual function void randomize_ack();
    `DV_CHECK_STD_RANDOMIZE_FATAL(acknack);
    case (acknack)
      i2c_pkg::ACK:  req.drv_type = DevAck;
      i2c_pkg::NACK: req.drv_type = DevNack;
      default: `uvm_fatal(`gfn, "Shouldn't get here!")
    endcase
  endfunction : randomize_ack


  virtual task drive_addr_byte_ack();
    `uvm_create_obj(REQ, req);
    start_item(req);

    // The base class / default behaviour is to ACK all address bytes.
    // Here, choose randomly between ACK and NACK.
    randomize_ack();
    if (req.drv_type == DevNack) `uvm_info(`gfn, "NACKing the address byte!", UVM_LOW)

    finish_item(req);
  endtask : drive_addr_byte_ack


  virtual task drive_write_byte_ack();
    `uvm_create_obj(REQ, req);
    start_item(req);

    randomize_ack();
    if (req.drv_type == DevNack) `uvm_info(`gfn, "NACKing a data byte!", UVM_LOW)

    finish_item(req);
  endtask : drive_write_byte_ack


endclass : i2c_target_may_nack_seq
