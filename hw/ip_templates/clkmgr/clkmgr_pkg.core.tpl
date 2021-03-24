CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:clkmgr_pkg:0.1")}
description: "Clock manager package"

filesets:
  files_rtl:
    depend:
      - lowrisc:constants:top_pkg
      - lowrisc:ip:pwrmgr_pkg
    files:
      - rtl/clkmgr_pkg.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    filesets:
      - files_rtl
