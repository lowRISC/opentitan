CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_if:0.1")}
description: "GPIO Interfaces"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}:0.1")}
    files:
      - ${module_instance_name}_straps_if.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
