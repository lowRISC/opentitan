CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:alert_handler:0.1")}
description: "Alert Handler"
virtual:
  - lowrisc:ip_interfaces:alert_handler

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:alert_handler_component:0.1")}
      - ${instance_vlnv("lowrisc:ip_interfaces:alert_handler_reg:0.1")}
    file_type: systemVerilogSource
% if len(virtual_pkg_vlnv) > 0:
  files_virtual_provider:
    depend:
      - "fileset_top ? (${virtual_pkg_vlnv})"
% endif

parameters:
  SYNTHESIS:
    datatype: bool
    paramtype: vlogdefine


targets:
  default: &default_target
    filesets:
      - files_rtl
    toplevel: alert_handler

  lint:
    <<: *default_target
% if len(virtual_pkg_vlnv) > 0:
    filesets_append:
      - files_virtual_provider
% endif
    default_tool: verilator
    parameters:
      - SYNTHESIS=true
    tools:
      verilator:
        mode: lint-only
        verilator_options:
          - "-Wall"
