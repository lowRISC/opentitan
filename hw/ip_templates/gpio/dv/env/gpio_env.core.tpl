CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_env:0.1")}
description: "GPIO DV UVM environmnt"
filesets:
  files_dv:
    depend:
      - lowrisc:dv:ralgen
      - lowrisc:dv:cip_lib
    files:
      - ${module_instance_name}_env_pkg.sv
      - ${module_instance_name}_env_cfg.sv: {is_include_file: true}
      - ${module_instance_name}_env_cov.sv: {is_include_file: true}
      - ${module_instance_name}_scoreboard.sv: {is_include_file: true}
      - ${module_instance_name}_env.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_vseq_list.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_base_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_common_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_smoke_vseq.sv: {is_include_file: true}
% if num_inp_period_counters > 0:
      - seq_lib/${module_instance_name}_inp_prd_cnt_vseq.sv: {is_include_file: true}
% endif
      - seq_lib/${module_instance_name}_rand_intr_trigger_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_random_dout_din_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_dout_din_regs_random_rw_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_random_long_reg_writes_reg_reads_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_filter_stress_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_full_random_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_stress_all_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_intr_rand_pgm_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_intr_with_filter_rand_intr_event_vseq.sv: {is_include_file: true}
      - seq_lib/${module_instance_name}_rand_straps_vseq.sv : {is_include_file: true}
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
