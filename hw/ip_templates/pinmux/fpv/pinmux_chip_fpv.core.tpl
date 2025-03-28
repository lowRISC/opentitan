CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:systems:pinmux_chip_fpv:0.1")}
description: "pinmux FPV target with chip_earlgrey parameters"

filesets:
  files_formal:
    depend:
      - lowrisc:prim:all
      - lowrisc:ip:tlul
      - lowrisc:ip:jtag_pkg
      - lowrisc:prim:mubi_pkg
      - lowrisc:ip:lc_ctrl_pkg
      - ${instance_vlnv("lowrisc:ip:pinmux:0.1")}
      - lowrisc:fpv:csr_assert_gen
      - ${instance_vlnv("lowrisc:fpv:pinmux_common_fpv:0.1")}
      - ${instance_vlnv("lowrisc:constants:top_pkg")}
      - ${instance_vlnv("lowrisc:systems:scan_role_pkg")}
    files:
      - tb/pinmux_chip_tb.sv
    file_type: systemVerilogSource

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
    toplevel: pinmux_chip_tb

  formal:
    <<: *default_target

  lint:
    <<: *default_target
