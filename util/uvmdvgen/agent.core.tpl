CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "${vendor}:dv:${name}_agent:0.1"
description: "${name.upper()} DV UVM agent"
filesets:
  files_dv:
    depend:
      - lowrisc:dv:dv_utils
      - lowrisc:dv:dv_lib
    files:
      - ${name}_if.sv
      - ${name}_agent_pkg.sv
      - ${name}_item.sv: {is_include_file: true}
      - ${name}_agent_cfg.sv: {is_include_file: true}
      - ${name}_agent_cov.sv: {is_include_file: true}
% if has_separate_host_device_driver:
      - ${name}_host_driver.sv: {is_include_file: true}
      - ${name}_device_driver.sv: {is_include_file: true}
% else:
      - ${name}_driver.sv: {is_include_file: true}
% endif
      - ${name}_monitor.sv: {is_include_file: true}
      - ${name}_agent.sv: {is_include_file: true}
      - seq_lib/${name}_base_seq.sv: {is_include_file: true}
      - seq_lib/${name}_seq_list.sv: {is_include_file: true}
    file_type: systemVerilogSource

targets:
  default:
    filesets:
      - files_dv
