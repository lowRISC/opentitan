// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I2C Agent sequence which behaves as an I2C TARGET.
//
// - Uses the base-class hooks which determine that state of an inprogress transfer.
// - Each time the I2C-Target is required to ACK/NACk during a transfer, this sequence randomly
//   selects between an ACK or NACK.
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

  // Return DevAck or DevNack with equal probability
  protected virtual function drv_type_e get_ack_nack();
    return ($urandom_range(0,1) ? DevAck : DevNack);
  endfunction

endclass : i2c_target_may_nack_seq
