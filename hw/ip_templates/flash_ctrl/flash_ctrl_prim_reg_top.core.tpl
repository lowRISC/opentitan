CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:flash_ctrl_prim_reg_top:1.0")}
description: "Generic register top for the FLASH wrapper"
virtual:
  - lowrisc:ip_interfaces:flash_ctrl_prim_reg_top

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:flash_ctrl_pkg")}
      - lowrisc:prim:subreg
    files:
      - rtl/flash_ctrl_prim_reg_top.sv
    file_type: systemVerilogSource


parameters:
  SYNTHESIS:
    datatype: bool
    paramtype: vlogdefine


targets:
  default: &default_target
    filesets:
      - files_rtl
    toplevel: lc_ctrl
