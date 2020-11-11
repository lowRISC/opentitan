CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "${vendor}:dv:${name}_env:0.1"
description: "${name.upper()} DV UVM environment"
filesets:
  files_dv:
    depend:
% if has_ral:
      - lowrisc:dv:ralgen
% endif
% if is_cip:
      - lowrisc:dv:cip_lib
% else:
      - lowrisc:dv:dv_lib
% endif
% for agent in env_agents:
      - ${vendor}:dv:${agent}_agent
% endfor
    files:
      - ${name}_env_pkg.sv
      - ${name}_env_cfg.sv: {is_include_file: true}
      - ${name}_env_cov.sv: {is_include_file: true}
      - ${name}_virtual_sequencer.sv: {is_include_file: true}
      - ${name}_scoreboard.sv: {is_include_file: true}
      - ${name}_env.sv: {is_include_file: true}
      - seq_lib/${name}_vseq_list.sv: {is_include_file: true}
      - seq_lib/${name}_base_vseq.sv: {is_include_file: true}
      - seq_lib/${name}_common_vseq.sv: {is_include_file: true}
      - seq_lib/${name}_smoke_vseq.sv: {is_include_file: true}
    file_type: systemVerilogSource

% if has_ral:
generate:
  ral:
    generator: ralgen
    parameters:
      name: ${name}
      ip_hjson: ../../data/${name}.hjson
% endif

targets:
  default:
    filesets:
      - files_dv
% if has_ral:
    generate:
      - ral
% endif
