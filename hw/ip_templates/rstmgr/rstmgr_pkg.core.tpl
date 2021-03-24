CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:rstmgr_pkg:0.1")}
description: "Reset manager package"

filesets:
  files_rtl:
    depend:
      - "fileset_topgen ? (lowrisc:systems:topgen)"
    files:
      - rtl/rstmgr_pkg.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
