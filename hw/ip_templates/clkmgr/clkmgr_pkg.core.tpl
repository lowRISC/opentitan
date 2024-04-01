CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:systems:clkmgr_pkg:0.1")}
description: "Top specific clock manager package"
virtual:
  - lowrisc:ip_interfaces:clkmgr_pkg

filesets:
  files_rtl:
    depend:
      - lowrisc:constants:top_pkg
      - lowrisc:ip_interfaces:pwrmgr_pkg
      - lowrisc:prim:mubi
    files:
      - rtl/clkmgr_pkg.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    filesets:
      - files_rtl
