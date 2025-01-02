CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:pwrmgr:0.1")}
description: "Power manager RTL"
virtual:
  - lowrisc:ip_interfaces:pwrmgr

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:pwrmgr_pkg:0.1")}
      - ${instance_vlnv("lowrisc:ip:pwrmgr_reg:0.1")}
      - lowrisc:ip:rv_core_ibex_pkg
      - lowrisc:ip:pwrmgr_component
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/pwrmgr.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/pwrmgr.waiver
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
    toplevel: pwrmgr

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
