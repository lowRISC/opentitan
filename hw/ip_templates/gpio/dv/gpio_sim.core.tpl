CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sim:0.1")}
description: "${module_instance_name.upper()} DV sim target"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}:0.1")}

  files_dv:
    depend:
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_test")}
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sva")}
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_if")}
    files:
      - tb/tb.sv
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
