CAPI=2:
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
${gen_core_comment}
name: "lowrisc:dv:rstmgr_ral:0.1"
description: "RSTMGR DV ralgen collateral"
filesets:
  files_dv:
    depend:
      - lowrisc:dv:ralgen

generate:
  ral:
    generator: ralgen
    parameters:
      name: rstmgr
      ip_hjson: ../../../data/autogen/rstmgr.hjson

targets:
  default:
    filesets:
      - files_dv
    generate:
      - ral
