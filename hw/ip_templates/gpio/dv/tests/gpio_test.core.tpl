CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_test:0.1")}
description: "GPIO DV UVM test"
filesets:
  files_dv:
    depend:
      - ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_env:0.1")}
    files:
      - ${module_instance_name}_test_pkg.sv
      - ${module_instance_name}_base_test.sv: {is_include_file: true}
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
