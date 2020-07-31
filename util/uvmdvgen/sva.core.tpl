CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: "lowrisc:dv:${name}_sva:0.1"
description: "${name.upper()} assertion modules and bind file."
filesets:
  files_dv:
    depend:
      - lowrisc:tlul:headers
% if has_ral:
      - lowrisc:fpv:csr_assert_gen
% endif
    files:
      - ${name}_bind.sv
    file_type: systemVerilogSource

% if has_ral:
generate:
  csr_assert_gen:
    generator: csr_assert_gen
    parameters:
      spec: ../../data/${name}.hjson
      depend: lowrisc:ip:${name}
% endif

targets:
  default:
    filesets:
      - files_dv
% if has_ral:
    generate:
      - csr_assert_gen
% endif
