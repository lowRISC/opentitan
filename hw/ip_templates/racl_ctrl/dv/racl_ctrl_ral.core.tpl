CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_ral:0.1")}
description: "RACL_CTRL register model"
virtual:
  - "lowrisc:dv:racl_ctrl_ral"
filesets:
  ral_dep:
    depend:
      - lowrisc:dv:ralgen

generate:
  ral:
    generator: ralgen
    parameters:
      name: racl_ctrl
      ip_hjson: ../data/${module_instance_name}.hjson
    position: prepend

targets:
  default:
    filesets:
      - ral_dep
    generate:
      - ral
