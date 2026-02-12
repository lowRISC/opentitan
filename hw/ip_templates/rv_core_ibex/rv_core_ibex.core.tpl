CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:ip:{module_instance_name}:0.1")}
description: "Wrapper around ibex with TL-UL ports"
filesets:
  files_rtl:
    depend:
      - lowrisc:ibex:ibex_top
      - lowrisc:ip:lc_ctrl_pkg
      - lowrisc:ip:otp_ctrl_pkg
      - lowrisc:ip:tlul
      - lowrisc:prim:all
      - lowrisc:prim:clock_gating
      - lowrisc:prim:edn_req
      - lowrisc:prim:esc
      - lowrisc:prim:lc_sync
      - lowrisc:prim:lc_sender
      - lowrisc:prim:mubi
      - lowrisc:tlul:adapter_host
      - lowrisc:ip:rv_core_ibex_pkg
    % if racl_support:
      - ${instance_vlnv("lowrisc:constants:top_racl_pkg")}
    % endif

    files:
      - rtl/${module_instance_name}_reg_pkg.sv
      - rtl/${module_instance_name}_cfg_reg_top.sv
      - rtl/${module_instance_name}_addr_trans.sv
      - rtl/${module_instance_name}.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
    files:
      - lint/rv_core_ibex.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
    files:
      - lint/${module_instance_name}.waiver
    file_type: waiver

  files_veriblelint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
    files:
      - lint/${module_instance_name}.vbl
    file_type: waiver

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

  syn:
    <<: *default_target
    # TODO: set default to DC once
    # this option is available
    # olofk/edalize#89
    default_tool: icarus
    parameters:
      - SYNTHESIS=true
