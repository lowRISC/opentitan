CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:ac_range_check_env:0.1")}
description: "AC_RANGE_CHECK DV UVM environment"
filesets:
  files_dv:
    depend:
      - lowrisc:dv:ralgen
      - lowrisc:dv:cip_lib
      - lowrisc:dv:dv_base_reg
      - lowrisc:dv:dv_lib
    files:
      - ac_range_check_env_pkg.sv
      - ac_range_check_dut_cfg.sv: {is_include_file: true}
      - ac_range_check_scb_item.sv: {is_include_file: true}
      - ac_range_check_env_cfg.sv: {is_include_file: true}
      - ac_range_check_env_cov.sv: {is_include_file: true}
      - ac_range_check_virtual_sequencer.sv: {is_include_file: true}
      - ac_range_check_predictor.sv: {is_include_file: true}
      - ac_range_check_scoreboard.sv: {is_include_file: true}
      - ac_range_check_env.sv: {is_include_file: true}
      - seq_lib/ac_range_check_vseq_list.sv: {is_include_file: true}
      - seq_lib/ac_range_check_base_vseq.sv: {is_include_file: true}
      - seq_lib/ac_range_check_common_vseq.sv: {is_include_file: true}
      - seq_lib/ac_range_check_smoke_vseq.sv: {is_include_file: true}
      - seq_lib/ac_range_check_smoke_racl_vseq.sv: {is_include_file: true}
    file_type: systemVerilogSource

generate:
  ral:
    generator: ralgen
    parameters:
      name: ac_range_check
      ip_hjson: ../../data/${module_instance_name}.hjson
    position: prepend

targets:
  default:
    filesets:
      - files_dv
    generate:
      - ral
