CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

name: "${package}"
description: "${description}"
% if virtual_package is not UNDEFINED:
virtual:
  - ${virtual_package}
% endif

filesets:
  files_rtl:
  % if dependencies is not UNDEFINED:
    depend:
    % for dep in dependencies:
      - ${dep}
    % endfor
  % endif
    files:
    % for file in files:
      - ${file}
    % endfor
    file_type: systemVerilogSource

  % if files_veriblelint_waiver is not UNDEFINED:
  files_veriblelint_waiver:
    depend:
      - lowrisc:lint:common
      - lowrisc:lint:comportable
    files:
      - ${files_veriblelint_waiver}
    file_type: veriblelintWaiver

  % endif
targets:
  default:
    filesets:
      - files_rtl
    % if files_veriblelint_waiver is not UNDEFINED:
      - tool_veriblelint ? (files_veriblelint_waiver)
    % endif
