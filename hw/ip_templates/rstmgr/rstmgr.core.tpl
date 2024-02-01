CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:rstmgr:0.1")}
description: "Reset manager RTL"
virtual:
  - lowrisc:ip_interfaces:rstmgr

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:alert_handler_component
      - lowrisc:ip:rv_core_ibex_pkg
      - lowrisc:ip:tlul
      - lowrisc:prim:clock_mux2
      - lowrisc:prim:esc
      - lowrisc:prim:lc_sync
      - lowrisc:prim:mubi
      - lowrisc:prim:clock_buf
      - lowrisc:prim:sparse_fsm
      - ${instance_vlnv("lowrisc:ip:rstmgr_pkg:0.1")}
      - ${instance_vlnv("lowrisc:ip:rstmgr_reg:0.1")}
      - lowrisc:ip:rstmgr_cnsty_chk
    files:
      - rtl/rstmgr_ctrl.sv
      - rtl/rstmgr_por.sv
      - rtl/rstmgr_crash_info.sv
      - rtl/rstmgr_leaf_rst.sv
      - rtl/rstmgr.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/rstmgr.waiver
    file_type: waiver

parameters:
  SYNTHESIS:
    datatype: bool
    paramtype: vlogdefine


targets:
  default: &default_target
    filesets:
      - tool_verilator  ? (files_verilator_waiver)
      - tool_ascentlint ? (files_ascentlint_waiver)
      - files_rtl
    toplevel: rstmgr

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
