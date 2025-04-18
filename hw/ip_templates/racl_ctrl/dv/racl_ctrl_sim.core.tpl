CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:racl_ctrl_sim:0.1")}
description: "A racl_ctrl simulation"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:constants:top_racl_pkg")}
      - ${instance_vlnv("lowrisc:ip:racl_ctrl")}

  files_dv:
    depend:
      - lowrisc:dv:racl_ctrl_test
      - ${instance_vlnv("lowrisc:dv:racl_ctrl_sva")}
    files:
      - tb.sv
    file_type: systemVerilogSource


targets:
  sim: &sim_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv
    default_tool: vcs

  # TODO: add a lint check cfg in `hw/top_earlgrey/lint/top_*_dv_lint_cfgs.hjson`
  lint:
    <<: *sim_target
