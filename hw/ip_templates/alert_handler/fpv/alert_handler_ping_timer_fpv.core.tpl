CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:fpv:{module_instance_name}_ping_timer_fpv:0.1")}
description: "${module_instance_name.upper()} FPV target"
filesets:
  files_formal:
    depend:
      - lowrisc:prim:all
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}")}
    files:
      - vip/${module_instance_name}_ping_timer_assert_fpv.sv
      - tb/${module_instance_name}_ping_timer_bind_fpv.sv
      - tb/${module_instance_name}_ping_timer_tb.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    # note, this setting is just used
    # to generate a file list for jg
    default_tool: icarus
    filesets:
      - files_formal
    toplevel: ${module_instance_name}_ping_timer_tb

  formal:
    <<: *default_target

  lint:
    <<: *default_target
