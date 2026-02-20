CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
<%
module_name = instance_vlnv("lowrisc:ip:" + module_instance_name + "_fpv:0.1")
depends_name = instance_vlnv("lowrisc:ip:" + module_instance_name)
%>\
name: ${module_name}
description: "FPV for RstMgr"

filesets:
  files_formal:
    depend:
      - ${depends_name}
      - lowrisc:fpv:csr_assert_gen
      - ${instance_vlnv("lowrisc:dv:rstmgr_sva:0.1")}
    files:
      - tb/${module_instance_name}_fpv_bind.sv
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
    toplevel: ${module_instance_name}

  formal:
    <<: *default_target

  lint:
    <<: *default_target
