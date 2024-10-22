// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Top level dut name (sv module).
  name: pinmux

  // Fusesoc core file used for building the file list.
  fusesoc_core: lowrisc:ip_interfaces:pinmux:0.1

  import_cfgs: [// Project wide common synthesis config file
                "{proj_root}/hw/syn/tools/dvsim/common_syn_cfg.hjson"],

  // Timing constraints for this module
  sdc_file: "{proj_root}/hw/top_${topname}/ip_autogen/pinmux/syn/constraints.sdc"

  // Technology specific timing constraints for this module
  foundry_sdc_file: "{foundry_root}/top_${topname}/syn/foundry.constraints.sdc"
}
