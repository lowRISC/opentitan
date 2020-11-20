// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package sensor_ctrl_pkg;

  parameter int NumAlerts   = sensor_ctrl_reg_pkg::NumAlerts;
  parameter int NumIoRails  = sensor_ctrl_reg_pkg::NumIoRails;

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;

endpackage // sensor_ctrl_pkg
