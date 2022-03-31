CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
<%
module_name = instance_vlnv("lowrisc:ip:" + module_instance_name + "_fpv:0.1")
depends_name = instance_vlnv("lowrisc:ip:" + module_instance_name)
%>\
name: ${module_name}
description: "FPV for RISC-V PLIC"

filesets:
  files_formal:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:prim:all
      - ${depends_name}
      - lowrisc:fpv:csr_assert_gen
    files:
      - tb/${module_instance_name}_bind_fpv.sv
      - tb/${module_instance_name}_tb.sv
      - vip/${module_instance_name}_assert_fpv.sv
    file_type: systemVerilogSource


generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../data/${module_instance_name}.hjson
      depend: ${depends_name}

targets:
  default: &default_target
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
    generate:
      - csr_assert_gen
    toplevel: ${module_instance_name}_tb

  formal:
    <<: *default_target

  lint:
    <<: *default_target
