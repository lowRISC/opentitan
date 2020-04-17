CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:fpv:rv_plic_fpv:0.1"
description: "FPV genenric testbench for RISC-V PLIC example"

filesets:
  files_formal:
    depend:
      - lowrisc:fpv:rv_plic_component_fpv
      - lowrisc:top_earlgrey:rv_plic
    files:
      - rv_plic_csr_assert_fpv.sv
      - rv_plic_bind_fpv.sv
      - rv_plic_fpv.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
    toplevel: rv_plic_fpv

  formal:
    <<: *default_target
