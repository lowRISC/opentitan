CAPI=2:
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Note: This is theThis is the "guts" of the testbench, but won't quite work on its own because it isn't
# templated, so can't depend on the specific instantiation for the top we're interested in. See
# hw/top_*/ip_autogen/racl_ctrl/dv for the instantiated version.
name: ${instance_vlnv("lowrisc:dv:racl_ctrl_sim:0.1")}
description: "The core of a racl_ctrl simulation"
filesets:
  default:
    depend:
      - lowrisc:systems:top_${topname}_racl_pkg
      - ${instance_vlnv("lowrisc:ip:racl_ctrl")}
      - lowrisc:dv:racl_ctrl_sim_core

targets:
  sim: &sim_target
    toplevel: tb
    filesets:
      - default
    default_tool: vcs

  # TODO: add a lint check cfg in `hw/top_earlgrey/lint/top_*_dv_lint_cfgs.hjson`
  lint:
    <<: *sim_target
