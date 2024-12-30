CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:fpv:pinmux_fpv:0.1")}
description: "pinmux FPV target"
filesets:
  files_formal:
    depend:
      - lowrisc:prim:all
      - lowrisc:ip:tlul
      - ${instance_vlnv("lowrisc:ip:pinmux:0.1")}
      - lowrisc:fpv:csr_assert_gen
      - ${instance_vlnv("lowrisc:fpv:pinmux_common_fpv")}
      - lowrisc:systems:scan_role_pkg
    files:
      - tb/pinmux_tb.sv
    file_type: systemVerilogSource
% if len(virtual_pkg_vlnv) > 0:
  files_virtual_provider:
    depend:
      - "fileset_top ? (${virtual_pkg_vlnv})"
% endif

generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../data/pinmux.hjson

targets:
  default: &default_target
    default_tool: icarus
    filesets:
      - files_formal
    generate:
      - csr_assert_gen
    toplevel: pinmux_tb

  formal:
    <<: *default_target
    filesets_append:
% if len(virtual_pkg_vlnv) > 0:
      - files_virtual_provider
% endif

  lint:
    <<: *default_target
    filesets_append:
% if len(virtual_pkg_vlnv) > 0:
      - files_virtual_provider
% endif
