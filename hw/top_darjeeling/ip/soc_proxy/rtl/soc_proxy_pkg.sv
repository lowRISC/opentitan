// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package soc_proxy_pkg;

  // Alert interface types
  typedef struct packed {
    logic alert_p;
    logic alert_n;
  } soc_alert_req_t;
  typedef struct packed {
    logic ack_p;
    logic ack_n;
  } soc_alert_rsp_t;

  // Default values for alert interface types
  parameter soc_alert_req_t SOC_ALERT_REQ_DEFAULT = '{alert_p: 1'b0, alert_n: 1'b1};
  parameter soc_alert_rsp_t SOC_ALERT_RSP_DEFAULT = '{ack_p: 1'b0, ack_n: 1'b1};

  // This defines the index of each of SoC Proxy's alerts.  If you add, change, or remove an alert,
  // update this enum as well.
  typedef enum logic [$clog2(soc_proxy_reg_pkg::NumAlerts+1)-1:0] {
    FatalAlertIntg,
    FatalAlertExternal0,
    FatalAlertExternal1,
    FatalAlertExternal2,
    FatalAlertExternal3,
    FatalAlertExternal4,
    FatalAlertExternal5,
    FatalAlertExternal6,
    FatalAlertExternal7,
    RecovAlertExternal0,
    RecovAlertExternal1,
    RecovAlertExternal2,
    RecovAlertExternal3,
    RecovAlertExternal4,
    RecovAlertExternal5,
    RecovAlertExternal6,
    RecovAlertExternal7,
    NumAlertSources
  } soc_proxy_alert_e;

  // Assertions on these constants are part of the `soc_proxy` module (since they can't be put into
  // this package).
  localparam int unsigned NumInternalAlerts = FatalAlertIntg - FatalAlertIntg + 1;
  localparam int unsigned NumFatalExternalAlerts = FatalAlertExternal7 - FatalAlertExternal0 + 1;
  localparam int unsigned NumRecovExternalAlerts = RecovAlertExternal7 - RecovAlertExternal0 + 1;
  localparam int unsigned NumExternalAlerts = NumFatalExternalAlerts + NumRecovExternalAlerts;

endpackage
