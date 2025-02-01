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
      - ${instance_vlnv(f"lowrisc:ip:{module_instance_name}_pkg:0.1")}
      - lowrisc:prim:mubi_pkg
      - ${top_pkg_vlnv}
    files:
      - ${module_instance_name}_env_pkg.sv
      - ${module_instance_name}_if.sv
      - ${module_instance_name}_env_cfg.sv: {is_include_file: true}
      - ${module_instance_name}_env_cov.sv: {is_include_file: true}
      - ${module_instance_name}_virtual_sequencer.sv: {is_include_file: true}
      - ${module_instance_name}_scoreboard.sv: {is_include_file: true}
      - ${module_instance_name}_env.sv: {is_include_file: true}
      - seq_lib/alert_handler_vseq_list.sv: {is_include_file: true}
      - seq_lib/alert_handler_base_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_common_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_smoke_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_random_alerts_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_random_classes_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_esc_intr_timeout_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_esc_alert_accum_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_sig_int_fail_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_entropy_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_ping_timeout_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_lpg_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_lpg_stub_clk_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_entropy_stress_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_stress_all_vseq.sv: {is_include_file: true}
      - seq_lib/alert_handler_alert_accum_saturation_vseq.sv: {is_include_file: true}
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
