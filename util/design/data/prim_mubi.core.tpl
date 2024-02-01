CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
#
#    util/design/gen-mubi.py
#
name: "lowrisc:prim:mubi:0.1"
description: "Multibit types and functions"
filesets:
  files_rtl:
    depend:
      - lowrisc:prim:assert
      - lowrisc:prim:buf
      - lowrisc:prim:flop
    files:
      - rtl/prim_mubi_pkg.sv
% for n in range(1, n_max_nibbles+1):
      - rtl/prim_mubi${4*n}_sender.sv
      - rtl/prim_mubi${4*n}_sync.sv
      - rtl/prim_mubi${4*n}_dec.sv
% endfor
    file_type: systemVerilogSource

  files_verilator_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common

  files_ascentlint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common
    files:
      - lint/prim_mubi.waiver
    file_type: waiver

  files_veriblelint_waiver:
    depend:
      # common waivers
      - lowrisc:lint:common

targets:
  default: &default_target
    filesets:
      - tool_verilator   ? (files_verilator_waiver)
      - tool_ascentlint  ? (files_ascentlint_waiver)
      - tool_veriblelint ? (files_veriblelint_waiver)
      - files_rtl

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
