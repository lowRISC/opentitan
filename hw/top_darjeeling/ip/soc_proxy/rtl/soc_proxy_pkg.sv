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
    FatalAlertExternal8,
    FatalAlertExternal9,
    FatalAlertExternal10,
    FatalAlertExternal11,
    FatalAlertExternal12,
    FatalAlertExternal13,
    FatalAlertExternal14,
    FatalAlertExternal15,
    FatalAlertExternal16,
    FatalAlertExternal17,
    FatalAlertExternal18,
    FatalAlertExternal19,
    FatalAlertExternal20,
    FatalAlertExternal21,
    FatalAlertExternal22,
    FatalAlertExternal23,
    RecovAlertExternal0,
    RecovAlertExternal1,
    RecovAlertExternal2,
    RecovAlertExternal3,
    NumAlertSources
  } soc_proxy_alert_e;

  localparam int unsigned NumSocGpio = 16;
  // Assertions on these constants are part of the `soc_proxy` module (since they can't be put into
  // this package).
  localparam int unsigned NumInternalAlerts = FatalAlertIntg - FatalAlertIntg + 1;
  parameter  int unsigned NumFatalExternalAlerts = FatalAlertExternal23 - FatalAlertExternal0 + 1;
  parameter  int unsigned NumRecovExternalAlerts = RecovAlertExternal3 - RecovAlertExternal0 + 1;
  localparam int unsigned NumExternalAlerts = NumFatalExternalAlerts + NumRecovExternalAlerts;

endpackage
