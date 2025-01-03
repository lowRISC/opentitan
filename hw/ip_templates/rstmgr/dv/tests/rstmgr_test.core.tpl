CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:rstmgr_test:0.1")}
description: "RSTMGR DV UVM test"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:dv:rstmgr_env:0.1")}
    files:
      - rstmgr_test_pkg.sv
      - rstmgr_base_test.sv: {is_include_file: true}
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
