// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  name: "${name}"
  // TODO: remove the common testplans if not applicable
  import_testplans: ["hw/dv/tools/dvsim/testplans/csr_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/mem_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/intr_test_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/tl_device_access_types_testplan.hjson"]
  testpoints: [
    {
      name: smoke
      desc: '''
            Smoke test accessing a major datapath within the ${name}.

            **Stimulus**:
            - TBD

            **Checks**:
            - TBD
            '''
      milestone: V1
      tests: ["${name}_smoke"]
    }
    {
      name: feature1
      desc: '''Add more test entries here like above.'''
      milestone: V1
      tests: []
    }
  ]

  covergroups: [
    {
      name: ${name}_feature_cg
      desc: '''Describe the functionality covered by this covergroup.'''
    }
  ]
}
