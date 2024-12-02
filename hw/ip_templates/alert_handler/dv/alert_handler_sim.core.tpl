CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:alert_handler_sim:0.1")}
description: "ALERT_HANDLER DV sim target"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:alert_handler:0.1")}
    file_type: systemVerilogSource

  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:dv:alert_handler_tb:0.1")}
      - lowrisc:dv:alert_handler_cov
      - ${instance_vlnv("lowrisc:dv:alert_handler_sva:0.1")}
    file_type: systemVerilogSource

targets:
  sim: &sim_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv
    default_tool: vcs

  lint:
    <<: *sim_target
