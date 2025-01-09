CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:alert_handler_cov:0.1")}
description: "ALERT_HANDLER cov bind files"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:ip:alert_handler_component:0.1")}  # import alert_pkg
      - lowrisc:dv:dv_utils
    files:
      - alert_handler_cov_bind.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
