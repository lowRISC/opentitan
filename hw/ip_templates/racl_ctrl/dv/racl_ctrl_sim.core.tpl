CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sim:0.1")}
description: "A racl_ctrl simulation"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:constants:top_racl_pkg")}
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}")}

  files_dv:
    depend:
      - lowrisc:dv:racl_ctrl_test
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sva")}
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

  lint:
    <<: *sim_target
