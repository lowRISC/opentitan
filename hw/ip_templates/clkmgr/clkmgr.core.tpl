CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:clkmgr:0.1")}
description: "Clock Manager"

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:prim:all
      - lowrisc:prim:clock_gating
      - lowrisc:prim:clock_buf
      - lowrisc:prim:clock_div
      - lowrisc:ip:lc_ctrl_pkg
      - lowrisc:prim:lc_sync
      - lowrisc:prim:lc_sender
      - lowrisc:ip:pwrmgr_pkg
      - ${instance_vlnv("lowrisc:ip:clkmgr_pkg")}
    files:
      - rtl/clkmgr_reg_pkg.sv
      - rtl/clkmgr_reg_top.sv
      - rtl/clkmgr.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/clkmgr.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/clkmgr.waiver
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
    toplevel: clkmgr

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
