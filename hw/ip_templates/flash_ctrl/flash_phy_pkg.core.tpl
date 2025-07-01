CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:flash_phy_pkg:0.1")}
description: "Top specific flash phy package"
virtual:
  - lowrisc:virtual_ip:flash_phy_pkg

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:flash_ctrl_top_specific_pkg")}
      - ${instance_vlnv("lowrisc:ip:flash_phy_macro_pkg")}
    files:
      - rtl/flash_phy_pkg.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
