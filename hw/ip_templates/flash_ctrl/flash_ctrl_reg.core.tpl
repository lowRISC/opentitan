CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:flash_ctrl_reg:0.1")}
description: "Flash registers"

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - ${instance_vlnv("lowrisc:ip:flash_ctrl_top_specific_pkg")}
    files:
      - rtl/flash_ctrl_core_reg_top.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
