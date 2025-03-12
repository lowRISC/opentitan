CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:pinmux_pkg:0.1")}
description: "Pinmux package"
virtual:
  - lowrisc:virtual_ip:pinmux_pkg

filesets:
  files_rtl:
    depend:
      - lowrisc:prim:pad_wrapper_pkg
      - lowrisc:tlul:headers
    files:
      - rtl/pinmux_reg_pkg.sv
      - rtl/pinmux_pkg.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    filesets:
      - files_rtl
