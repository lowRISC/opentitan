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
    file_type: systemVerilogSource

  files_dv:
    depend:
      - lowrisc:dv:ralgen
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_tb:0.1")}
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_cov:0.1")}
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sva:0.1")}
    file_type: systemVerilogSource

generate:
  ral:
    generator: ralgen
    parameters:
      name: ${module_instance_name}
      ip_hjson: ../data/${module_instance_name}.hjson
    position: prepend

targets:
  sim: &sim_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv
    generate:
      - ral
    default_tool: vcs

  lint:
    <<: *sim_target
