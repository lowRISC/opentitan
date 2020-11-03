CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:fpv:${dut.name}_fpv:0.1"
description: "${dut.name} FPV target"
filesets:
  files_formal:
    depend:
% for dep in dut.deps:
      - ${dep}
  % if dut.is_cip:
      - lowrisc:fpv:csr_assert_gen
  % endif
% endfor
      # TODO: add more dependencies here if needed
    files:
      - vip/${dut.name}_assert_fpv.sv
      - tb/${dut.name}_bind_fpv.sv
      - tb/${dut.name}_fpv.sv
    file_type: systemVerilogSource

% if dut.is_cip:
generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../data/${dut_name}.hjson
      depend: lowrisc:ip:${dut_name}
% endif

targets:
  default: &default_target
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
% if dut.is_cip:
    generate:
      - csr_assert_gen
% endif
    toplevel: ${dut.name}_fpv

  formal:
    <<: *default_target

  lint:
    <<: *default_target
