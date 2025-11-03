CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_env:0.1")}
description: "${module_instance_name.upper()} DV UVM environment"
filesets:
  files_dv:
    depend:
      - lowrisc:dv:ralgen
      - lowrisc:dv:cip_lib
      - lowrisc:dv:dv_base_reg
      - lowrisc:dv:dv_lib
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}:0.1")}
    files:
      - ${module_instance_name}_env_pkg.sv
      - ac_range_check_dut_cfg.sv: {is_include_file: true}
      - ac_range_check_scb_item.sv: {is_include_file: true}
      - ${module_instance_name}_env_cfg.sv: {is_include_file: true}
      - ${module_instance_name}_env_cov.sv: {is_include_file: true}
      - ${module_instance_name}_virtual_sequencer.sv: {is_include_file: true}
      - ${module_instance_name}_predictor.sv: {is_include_file: true}
      - ${module_instance_name}_scoreboard.sv: {is_include_file: true}
      - ${module_instance_name}_env.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_vseq_list.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_base_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_common_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_smoke_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_smoke_racl_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_smoke_high_threshold_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_bypass_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_lock_range_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_stress_all_vseq.sv: {is_include_file: true}
    file_type: systemVerilogSource

generate:
  ral:
    generator: ralgen
    parameters:
      name: ${module_instance_name}
      ip_hjson: ../../data/${module_instance_name}.hjson
    position: prepend

targets:
  default:
    filesets:
      - files_dv
    generate:
      - ral
