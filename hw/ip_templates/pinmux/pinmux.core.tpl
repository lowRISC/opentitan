CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:ip:pinmux:0.1")}
description: "Pin Multiplexer"
virtual:
  - lowrisc:ip_interfaces:pinmux

filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:prim:all
      - lowrisc:prim:clock_buf
      - lowrisc:prim:buf
      - lowrisc:prim:lc_dec
      - lowrisc:prim:lc_sync
      - lowrisc:prim:lc_sender
      - lowrisc:prim:lc_or_hardened
      - lowrisc:prim:pad_wrapper_pkg
      - lowrisc:prim:pad_attr
      - lowrisc:ip:jtag_pkg
      - lowrisc:ip:usbdev
      - ${instance_vlnv("lowrisc:ip:pinmux_reg:0.1")}
      - lowrisc:ip_interfaces:pinmux_pkg
    files:
      - rtl/pinmux_wkup.sv
      - rtl/pinmux_jtag_buf.sv
      - rtl/pinmux_jtag_breakout.sv
    % if enable_strap_sampling:
      - rtl/pinmux_strap_sampling.sv
    % endif
      - rtl/pinmux.sv
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/pinmux.vlt
    file_type: vlt

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - lint/pinmux.waiver
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
    toplevel: pinmux

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

  formal:
    filesets:
      - files_rtl
    toplevel: pinmux_tb
