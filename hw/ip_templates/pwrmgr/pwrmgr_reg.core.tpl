CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:pwrmgr_reg:0.1")}
description: "Power manager registers"
virtual:
  - lowrisc:ip_interfaces:pwrmgr_reg

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - ${instance_vlnv("lowrisc:ip:pwrmgr_pkg")}
      - lowrisc:prim:subreg
      - lowrisc:tlul:headers
    files:
      - rtl/pwrmgr_reg_top.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
