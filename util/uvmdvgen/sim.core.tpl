CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:dv:${name}_sim:0.1"
description: "${name.upper()} DV sim target"
filesets:
  files_rtl:
    depend:
      - lowrisc:ip:${name}:0.1
    files:
      - tb/${name}_bind.sv
    file_type: systemVerilogSource

  files_dv:
    depend:
      - lowrisc:dv:${name}_test
    files:
      - tb/tb.sv
    file_type: systemVerilogSource

targets:
  sim:
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv
    default_tool: vcs
