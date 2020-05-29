// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  name: "${name}"
  // TODO: remove the common testplans if not applicable
  import_testplans: ["hw/dv/tools/testplans/csr_testplan.hjson",
                     "hw/dv/tools/testplans/mem_testplan.hjson",
                     "hw/dv/tools/testplans/intr_test_testplan.hjson",
                     "hw/dv/tools/testplans/tl_device_access_types_testplan.hjson"]
  entries: [
    {
      name: sanity
      desc: '''
            Basic sanity test acessing a major datapath within the ${name}.

            **Stimulus**:
            - TBD

            **Checks**:
            - TBD
            '''
      milestone: V1
      tests: ["${name}_sanity"]
    }
    {
      name: feature1
      desc: '''Add more test entries here like above.'''
      milestone: V1
      tests: []
    }
  ]
}
