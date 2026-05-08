// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // FI-specific overrides.
  overrides: [
    // Simulator used to sign off this block.
    {
      name: tool
      value: z01x
    }
    // Fusesoc core file used for building the file list.
    {
      name: fusesoc_core
      value: "${instance_vlnv("lowrisc:dv:flash_ctrl_fi_sim:0.1")}"
    }
    // Add the FI strobe module to the simulation tops.
    {
      name: sim_tops
      value: ["{tb}", "strobe"]
    }
  ]
}
