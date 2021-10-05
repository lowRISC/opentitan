CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
# PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
#
#    hw/ip/prim/util/generate_prim_mubi.py
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
% endfor
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
