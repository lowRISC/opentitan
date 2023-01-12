// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// i2c package
//
package i2c_pkg;
  typedef enum logic [1:0] {
    AcqData = 2'b00,
    AcqStart = 2'b01,
    AcqStop = 2'b10,
    AcqRestart = 2'b11
  } i2c_acq_byte_id_e;

endpackage : i2c_pkg
