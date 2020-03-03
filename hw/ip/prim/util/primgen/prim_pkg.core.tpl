CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:prim_abstract:prim_pkg:0.1"
description: "Constants used by the primitives"

filesets:
  files_rtl:
    files:
      - prim_pkg.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_rtl
