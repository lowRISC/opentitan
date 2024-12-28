CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:rstmgr_sim:0.1")}
description: "RSTMGR DV sim target"
filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:rstmgr")}

  files_dv:
    depend:
      - ${instance_vlnv("lowrisc:dv:rstmgr_test:0.1")}
      - ${instance_vlnv("lowrisc:dv:rstmgr_sva:0.1")}
    files:
      - tb.sv
      - cov/rstmgr_cov_bind.sv
    file_type: systemVerilogSource
<%
    have_files_top_sim = (len(alert_handler_instance_name) > 0 or
                          len(pwrmgr_instance_name) > 0)
%>\
% if have_files_top_sim:
  files_top_sim:
    depend:
%   if len(alert_handler_instance_name) > 0:
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:alert_handler_pkg:0.1", alert_handler_instance_name)})"
%   endif
%   if len(pwrmgr_instance_name) > 0:
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:pwrmgr_pkg:0.1", pwrmgr_instance_name)})"
      - "fileset_top ? (${instance_vlnv("lowrisc:ip:pwrmgr_rstmgr_sva_if:0.1", pwrmgr_instance_name)})"
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
