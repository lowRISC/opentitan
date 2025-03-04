CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:ip:{module_instance_name}:0.1")}
description: "gpio"
filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:prim:all
    files:
      - rtl/${module_instance_name}_pkg.sv
      - rtl/${module_instance_name}_reg_pkg.sv
      - rtl/${module_instance_name}_reg_top.sv
      - rtl/${module_instance_name}.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/gpio.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/${module_instance_name}.waiver
    file_type: waiver

  files_veriblelint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable

parameters:
  SYNTHESIS:
    datatype: bool
    paramtype: vlogdefine


targets:
  default: &default_target
    filesets:
      - tool_verilator   ? (files_verilator_waiver)
      - tool_ascentlint  ? (files_ascentlint_waiver)
      - tool_veriblelint ? (files_veriblelint_waiver)
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
