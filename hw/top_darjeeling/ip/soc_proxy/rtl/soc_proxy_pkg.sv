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

endpackage
