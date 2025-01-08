CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_cov:0.1")}
description: "${module_instance_name.upper()} cov bind files"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}_component:0.1")}  # import ${module_instance_name}_pkg
      - lowrisc:dv:dv_utils
    files:
      - ${module_instance_name}_cov_bind.sv
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
