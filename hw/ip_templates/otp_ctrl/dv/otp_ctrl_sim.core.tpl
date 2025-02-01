CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
name: ${instance_vlnv("lowrisc:dv:otp_ctrl_sim:0.1")}
description: "OTP_CTRL DV sim target"

filesets:
  files_rtl:
    depend:
      - ${instance_vlnv("lowrisc:ip:otp_ctrl")}

  files_dv:
    depend:
      - lowrisc:dv:mem_bkdr_util
      - ${instance_vlnv("lowrisc:dv:otp_ctrl_test")}
      - ${instance_vlnv("lowrisc:dv:otp_ctrl_sva")}
      - ${instance_vlnv("lowrisc:dv:otp_ctrl_cov")}
      # TODO: prim_pkg is deprecated
      - lowrisc:prim:prim_pkg
    files:
      - tb.sv
    file_type: systemVerilogSource

targets:
  default: &default_target
    toplevel: tb
    filesets:
      - files_rtl
      - files_dv

  sim:
    <<: *default_target
    default_tool: vcs

  lint:
    <<: *default_target
