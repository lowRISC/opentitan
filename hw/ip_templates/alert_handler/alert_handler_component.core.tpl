CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:ip:{module_instance_name}_component:0.1")}
description: "Alert Handler component without the CSRs"

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:prim:all
      - lowrisc:prim:esc
      - lowrisc:prim:double_lfsr
      - lowrisc:prim:count
      - lowrisc:prim:edn_req
      - lowrisc:prim:buf
      - lowrisc:prim:mubi
      - lowrisc:prim:sparse_fsm
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}_reg")}
    files:
      - rtl/${module_instance_name}_reg_wrap.sv
      - rtl/${module_instance_name}_lpg_ctrl.sv
      - rtl/${module_instance_name}_class.sv
      - rtl/${module_instance_name}_ping_timer.sv
      - rtl/${module_instance_name}_esc_timer.sv
      - rtl/${module_instance_name}_accu.sv
      - rtl/${module_instance_name}.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/alert_handler.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/alert_handler.waiver
    file_type: waiver

  files_veriblelint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable


targets:
  default: &default_target
    filesets:
      - tool_verilator   ? (files_verilator_waiver)
      - tool_ascentlint  ? (files_ascentlint_waiver)
      - tool_veriblelint ? (files_veriblelint_waiver)
      - files_rtl
