CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:clkmgr_test:0.1")}
description: "CLKMGR DV UVM test"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:dv:clkmgr_env:0.1")}
    files:
      - clkmgr_test_pkg.sv
      - clkmgr_base_test.sv: {is_include_file: true}
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
