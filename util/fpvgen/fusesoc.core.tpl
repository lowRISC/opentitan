CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:fpv:${dut.name}_fpv:0.1"
description: "${dut.name} FPV target"
filesets:
  files_fpv:
    depend:
% for dep in dut.deps:
      - ${dep}
% endfor
      # TODO: add more dependencies here if needed
    files:
      - vip/${dut.name}_assert_fpv.sv
      - tb/${dut.name}_bind_fpv.sv
      - tb/${dut.name}_fpv.sv
% if dut.is_cip:
      - vip/${dut.name}_csr_assert_fpv.sv
% endif
    file_type: systemVerilogSource

targets:
  default:
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_fpv
    toplevel: ${dut.name}_fpv
