// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

{
    name:               "${module_instance_name}",
    design_spec:        "../doc",
    dv_doc:             "../doc/dv",
    hw_checklist:       "../doc/checklist",
    sw_checklist:       "/sw/device/lib/dif/dif_rv_plic",
    revisions: [
      {
        version:            "1.0",
        life_stage:         "L1",
        design_stage:       "D3",
        verification_stage: "V2",
        dif_stage:          "S2",
        commit_id:          "",
        notes:              "Use FPV to perform block level verification.",
      }
    ],
}
