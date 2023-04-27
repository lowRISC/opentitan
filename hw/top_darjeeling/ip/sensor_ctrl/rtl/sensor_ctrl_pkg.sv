// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package sensor_ctrl_pkg;

  // alert position
  parameter int RecovAlert = 0;
  parameter int FatalAlert = 1;

  // Total events
  parameter int TotalEvents = sensor_ctrl_reg_pkg::NumAlertEvents +
                sensor_ctrl_reg_pkg::NumLocalEvents;

endpackage // sensor_ctrl_pkg
