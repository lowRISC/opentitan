CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:rstmgr_sva:0.1")}
description: "RSTMGR assertion modules and bind file."
filesets:
  files_dv:
    depend:
      - lowrisc:prim:mubi
      - ${instance_vlnv("lowrisc:ip:rstmgr_pkg:0.1")}
      - lowrisc:fpv:csr_assert_gen
      - ${instance_vlnv("lowrisc:dv:rstmgr_sva_ifs:0.1")}

    files:
      - rstmgr_bind.sv
    file_type: systemVerilogSource

generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../../data/rstmgr.hjson

targets:
  default: &default_target
    filesets:
      - files_dv
    generate:
      - csr_assert_gen
  formal:
    <<: *default_target
    filesets:
      - files_dv
    toplevel: rstmgr
