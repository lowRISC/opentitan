CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:flash_ctrl_sim:0.1")}
description: "FLASH_CTRL DV sim target"
filesets:
  files_rtl:
    depend:
      - lowrisc:ip:tlul
      - lowrisc:constants:top_pkg
      - ${instance_vlnv("lowrisc:ip:flash_ctrl:0.1")}
    file_type: systemVerilogSource

  files_dv:
    depend:
      - lowrisc:dv:mem_bkdr_util
      - ${instance_vlnv("lowrisc:dv:flash_ctrl_test")}
      - ${instance_vlnv("lowrisc:dv:flash_ctrl_sva")}
      - ${instance_vlnv("lowrisc:dv:flash_ctrl_cov")}
    files:
      - tb/tb.sv
    file_type: systemVerilogSource

% if len(pwrmgr_instance_name) > 0:
  files_top_sim:
    depend:
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:pwrmgr_pkg:0.1", pwrmgr_instance_name)})"
%endif

targets:
  default: &default_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv

  sim:
    <<: *default_target
% if len(pwrmgr_instance_name) > 0:
    filesets_append:
      - files_top_sim
% endif
    default_tool: vcs

  lint:
    <<: *default_target
% if len(pwrmgr_instance_name) > 0:
    filesets_append:
      - files_top_sim
% endif
