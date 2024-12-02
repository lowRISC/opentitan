CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:rv_plic:0.1")}
description: "RISC-V Platform Interrupt Controller (PLIC)"

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:rv_plic_component:0.1")}
      - lowrisc:ip:tlul
      - lowrisc:prim:subreg
    files:
      - rtl/${module_instance_name}_reg_pkg.sv
      - rtl/${module_instance_name}_reg_top.sv
      - rtl/${module_instance_name}.sv
    file_type: systemVerilogSource

parameters:
  SYNTHESIS:
    datatype: bool
    paramtype: vlogdefine

targets:
  default: &default_target
    filesets:
      - files_rtl
    toplevel: ${module_instance_name}

  lint:
    <<: *default_target
    default_tool: verilator
    parameters:
      - SYNTHESIS=true
    tools:
      verilator:
        mode: lint-only
        verilator_options:
          - "-Wall"
