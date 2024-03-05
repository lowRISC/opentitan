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
    // AcqNack means one of two things:
    // 1. We received a read request to our address, but had to NACK the
    // address because our ACQ FIFO is full.
    // 2. We received too many bytes in a write request and had to NACK a data
    // byte. The NACK'ed data byte is still in the data field for inspection.
    AcqNack      = 3'b100,
    // AcqNackStart menas that we got a write request to our address, we sent
    // an ACK to back to the host so that we can be compatible with SMBus, but
    // now we must unconditionally NACK the next byte. We cannot record that
    // NACK'ed byte because there is no space in the ACQ FIFO. The OpenTitan
    // software must know this distinction from a normal AcqNack because the
    // state machine must still continue through the AcquireByte and Nack*
    // states.
    AcqNackStart = 3'b101
  } i2c_acq_byte_id_e;

endpackage : i2c_pkg
