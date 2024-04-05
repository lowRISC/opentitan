// Copyright lowRISC contributors (OpenTitan project).
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
    // AcqNackStart means that we were addressed on this item, but we timed
    // out after stretching.
    AcqNackStart = 3'b101,
    // AcqNackStop means that we were addressed during the transaction, but we
    // timed out after stretching and received the Stop to end the
    // transaction.
    AcqNackStop  = 3'b110
  } i2c_acq_byte_id_e;

  // Width of each entry in the FMT FIFO with enough space for an 8-bit data
  // byte and 5 flags.
  parameter int unsigned FMT_FIFO_WIDTH = 8 + 5;

  // Width of each entry in the RX and TX FIFO: just an 8-bit data byte.
  parameter int unsigned RX_FIFO_WIDTH = 8;
  parameter int unsigned TX_FIFO_WIDTH = 8;

  // Width of each entry in the ACQ FIFO with enough space for an 8-bit data
  // byte and an identifier defined by i2c_acq_byte_id_e.
  parameter int unsigned ACQ_FIFO_WIDTH = I2C_ACQ_BYTE_ID_WIDTH + 8;

endpackage : i2c_pkg
