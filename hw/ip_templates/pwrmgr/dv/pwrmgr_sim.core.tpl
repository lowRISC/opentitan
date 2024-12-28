CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:pwrmgr_sim:0.1")}
description: "PWRMGR DV sim target"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:pwrmgr:0.1")}
  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:dv:pwrmgr_test:0.1")}
      - ${instance_vlnv("lowrisc:dv:pwrmgr_sva:0.1")}
      - ${instance_vlnv("lowrisc:dv:pwrmgr_unit_only_sva:0.1")}
    files:
      - tb.sv
      - cov/pwrmgr_cov_bind.sv
    file_type: systemVerilogSource
<%
    have_files_top_sim = (len(clkmgr_instance_name) > 0 or
                          len(alert_handler_instance_name) > 0)
%>\
% if have_files_top_sim:
  files_top_sim:
    depend:
%   if len(alert_handler_instance_name) > 0:
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:alert_handler_pkg:0.1", alert_handler_instance_name)})"
%   endif
%   if len(clkmgr_instance_name) > 0:
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:clkmgr_pwrmgr_sva_if:0.1", clkmgr_instance_name)})"
%   endif
% endif

targets:
  sim: &sim_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv
% if have_files_top_sim:
      - files_top_sim
% endif
    default_tool: vcs

  lint:
    <<: *sim_target
