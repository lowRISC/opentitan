// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// i2c package
//
package i2c_pkg;
  parameter int unsigned I2C_ACQ_BYTE_ID_WIDTH = 3;

  // TODO(#22028) encode this more efficiently in the ACQ FIFO. Each entry in the
  // ACQ FIFO does not need to contain both an 8 bit data field and a 3 bit
  // identifier. We should have the ACQ FIFO be 9 bits wide where the MSB
  // indicates whether it is a data byte or a control byte. This way we can
  // add more values to this enum without having to widen the ACQ FIFO width.
  typedef enum logic [I2C_ACQ_BYTE_ID_WIDTH-1:0] {
    AcqData      = 3'b000,
    AcqStart     = 3'b001,
    AcqStop      = 3'b010,
    AcqRestart   = 3'b011,
    AcqNack      = 3'b100
  } i2c_acq_byte_id_e;

endpackage : i2c_pkg
