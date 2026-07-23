CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

name: ${instance_vlnv("lowrisc:ip:" + module_instance_name + "_fpv:0.1")}
description: "FPV for Reset Manager"

filesets:
  files_formal:
    depend:
      - ${instance_vlnv("lowrisc:ip:" + module_instance_name)}
      - ${instance_vlnv("lowrisc:dv:rstmgr_sva:0.1")}
    files:
      - tb/rstmgr_fpv_tb.sv
      - ../dv/sva/rstmgr_bind.sv
    file_type: systemVerilogSource

generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../data/${module_instance_name}.hjson
      depend: ${instance_vlnv("lowrisc:ip:" + module_instance_name)}

targets:
  formal:
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
    generate:
      - csr_assert_gen
    toplevel: rstmgr_fpv_tb
