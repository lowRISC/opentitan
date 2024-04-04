CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:ip:${module_instance_name}_component:0.1"
description: "RISC-V Platform Interrupt Controller (PLIC)"

filesets:
  files_rtl:
    depend:
      - lowrisc:prim:assert
      - lowrisc:prim:alert
      - lowrisc:prim:max_tree
      - lowrisc:prim:flop_2sync
      - lowrisc:prim:reg_we_check
    files:
      - rtl/${module_instance_name}_gateway.sv
      - rtl/${module_instance_name}_target.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/${module_instance_name}.vlt
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

targets:
  default:
    filesets:
      - tool_verilator   ? (files_verilator_waiver)
      - tool_ascentlint  ? (files_ascentlint_waiver)
      - tool_veriblelint ? (files_veriblelint_waiver)
      - files_rtl
