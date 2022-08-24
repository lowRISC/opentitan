// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  name: "${module_instance_name}"
  import_testplans: ["hw/dv/tools/dvsim/testplans/fpv_csr_testplan.hjson"]
  testpoints: [
    {
      name: LevelTriggeredIp_A
      desc: '''If interrupt pending (`ip`) is triggered, and the level indicator is set to
            level triggered (`le=0`), then in the prvious clock cycle, the interrupt source
            (`intr_src_i) should be set to 1.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: EdgeTriggeredIp_A
      desc: '''If interrupt pending (`ip`) is triggered, and the level indicator is set to
            edge triggered (`le=1`), then in the prvious clock cycle, the interrupt source
            (`intr_src_i) should be at the rising edge.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: LevelTriggeredIpWithClaim_A
      desc: '''If `intr_src_i` is set to 1, level indicator is set to level triggered, and claim
            signal is not set, then at the next clock cycle `ip` will be triggered.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: EdgeTriggeredIpWithClaim_A
      desc: '''If `intr_src_i` is at the rising edge, level indicator is set to edge triggered, and claim
            signal is not set, then at the next clock cycle `ip` will be triggered.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: IpStableAfterTriggered_A
      desc: "Once `ip` is set, it stays stable until is being claimed."
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: IpClearAfterClaim_A
      desc: "Once `ip` is set and being claimed, its value is cleared to 0."
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: IpStableAfterClaimed_A
      desc: '''Once `ip` is cleared to 0, it stays stable until completed and being triggered
            again.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: TriggerIrqForwardCheck_A
      desc: '''If interrupt is enabled (`ie=1`), interrupt pending is set (`ip=1`), interrupt
            input has the highest priority among the rest of the inputs, and its priority is
            above the threshold. Then in the next clock clcye, the `irq_o` should be triggered,
            and the `irq_id_o` will reflect the input ID.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
    {
      name: TriggerIrqBackwardCheck_A
      desc: '''If `irq_o` is set to 1, then in the previous clock cycle, the corresponding
            `ip` should be set, `ie` should be enabled, and the interrupt source should above the
            threshold and have the highest priority.'''
      stage: V2
      tests: ["${module_instance_name}_assert"]

    }
    {
      name: IdChangeWithIrq_A
      desc: '''If `irq_id_o` signal is changed and the signal does not change to 0 (value 0 does
               not represent any interrupt source ID). Then either of the two condition should have
               happened:
               - `irq_o` is triggered
               - No interrupt triggered, `ip` is set and `ie` is enabled, interrupt source priority is the
                 largest among the rest of the interrupt, but the interrupt source
                 priority is smaller than the threshold'''
      stage: V2
      tests: ["${module_instance_name}_assert"]
    }
  ]
}
