CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_tb:0.1")}
description: "${module_instance_name.upper()} UVM TB environment"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_test:0.1")}
    files:
      - tb.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
