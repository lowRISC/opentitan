// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  name: "alert_handler"
  import_testplans: ["hw/dv/tools/dvsim/testplans/csr_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/intr_test_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/shadow_reg_errors_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/stress_all_with_reset_testplan.hjson",
                     "hw/dv/tools/dvsim/testplans/tl_device_access_types_testplan.hjson",
                     "hw/dv/sv/alert_esc_agent/data/alert_agent_basic_testplan.hjson",
                     "hw/dv/sv/alert_esc_agent/data/alert_agent_additional_testplan.hjson",
                     "hw/dv/sv/alert_esc_agent/data/esc_agent_basic_testplan.hjson",
                     "hw/dv/sv/alert_esc_agent/data/esc_agent_additional_testplan.hjson",
                     // Generated in IP gen area (hw/{top}/ip_autogen).
                     "alert_handler_sec_cm_testplan.hjson"]
  testpoints: [
    {
      name: smoke
      desc: '''
            - Alert_handler smoke test with one class configured that escalates through all
              phases after one alert has been triggered
            - Check interrupt pins, alert cause CSR values, escalation pings, and crashdump_o
              output values
            - Support both synchronous and asynchronous settings
            '''
      stage: V1
      tests: ["alert_handler_smoke"]
    }
    {
      name: esc_accum
      desc: '''
            Based on the smoke test, this test will focus on testing the escalation accumulation
            feature. So all the escalations in the test will be triggered by alert accumulation.
            '''
      stage: V2
      tests: ["alert_handler_esc_alert_accum"]
    }
    {
      name: esc_timeout
      desc: '''
           Based on the smoke test, this test will focus on testing the escalation timeout
           feature. So all the escalations in the test will be triggered by interrupt timeout.
           '''
      stage: V2
      tests: ["alert_handler_esc_intr_timeout"]
    }
    {
      name: entropy
      desc: '''
            Based on the smoke test, this test enables ping testing, and check if the ping feature
            correctly pings all devices within certain period of time.
            '''
      stage: V2
      tests: ["alert_handler_entropy"]
    }
    {
      name: sig_int_fail
      desc: '''
            This test will randomly inject differential pair failures on alert tx/rx pairs and the
            escalator tx/rx pairs. Then check if integrity failure alert is triggered and
            escalated.
            '''
      stage: V2
      tests: ["alert_handler_sig_int_fail"]
    }
    {
      name: clk_skew
      desc: '''
            This test will randomly inject clock skew within the differential pairs. Then check no
            alert is raised.
            '''
      stage: V2
      tests: ["alert_handler_smoke"]
    }
    {
      name: random_alerts
      desc: "Input random alerts and randomly write phase cycles."
      stage: V2
      tests: ["alert_handler_random_alerts"]
    }
    {
      name: random_classes
      desc: "Based on random_alerts test, this test will also randomly enable interrupt classes."
      stage: V2
      tests: ["alert_handler_random_classes"]
    }
    {
      name: ping_timeout
      desc: '''
            Based on entropy test, this test request alert_sender and esc_receiver drivers to
            randomly create ping requests timeout stimulus.

            Checks:
            - Verify interrupt pin and states.
            - Verify alert and local alert causes.
            - Verify escalation states and counts.
            '''
      stage: V2
      tests: ["alert_handler_ping_timeout"]
    }
    {
      name: lpg
      desc: '''
            Test alert_handler low_power_group(lpg) request.

            Stimulus:
            - Randomly enabled alert_receivers' `alert_en` but disable their ping response.
            - Turn on their low-power control by either set `lpg_cg_en_i` or `lpg_rst_en_i`.
              Or pause the alert_handler's clk input for a random period of time.
            - Enable alert ping timeout local alert.
            - Run alert_handler_entropy_vseq.

            Checks:
            - Expect no ping timeout error because the alert_receivers are disabled via low-power
              group, or because alert_handler's clk input is paused due to sleep mode.
            '''
      stage: V2
      tests: ["alert_handler_lpg", "alert_handler_lpg_stub_clk"]
    }
    {
      name: stress_all
      desc: '''
            Combine above sequences in one test to run sequentially with the following exclusions:
            - CSR sequences: scoreboard disabled
            - Ping_corner_cases sequence: included reset in the sequence
            '''
      stage: V2
      tests: ["alert_handler_stress_all"]
    }
    {
      name: alert_handler_entropy_stress_test
      desc: '''
            Stress the alert_handler's entropy request and make sure there is no spurious alert.

            Stimulus:
            - Randomly force the `wait_cyc_mask_i` to a legal value to stress the ping requests.
            - Wait for all alerts at least being pinged for a few times.
            Checks:
            - Check alert_cause and loc_alert_cause registers to make sure there is no spurious
              alert being fired.
            '''
      stage: V2
      tests: ["alert_handler_entropy_stress"]
    }

    {
      name: alert_handler_alert_accum_saturation
      desc: '''
            This sequence forces all four alert classes' accumulate counters to a large value that
            is close to the max saturation value.
            Then the sequence triggers alerts until the count saturates.

            Checks:
            - Check `accum_cnt` register does not overflow, but stays at the max value.
            - Check the correct interrupt fires if even the count saturates.
            '''
      stage: V2
      tests: ["alert_handler_alert_accum_saturation"]
    }
 ]

  covergroups: [
    {
      name: accum_cnt_cg
      desc: '''Covers escalation due to accumulated alerts.

            - Collect the threshold of accumulated alerts.
            - Collect which alert_class exceeds the accumulated count.
            - Cross the above coverpoints.
            '''
    }
    {
      name: intr_timeout_cnt_cg
      desc: '''Covers escalation due to interrupt timeout.

            - Collect the threshold of interrupt timeout cycles.
            - Collect which alert_class exceeds the timeout threshold.
            - Cross the above coverpoints.
            '''
    }
    {
      name: esc_sig_length_cg
      desc: '''Covers escalation signal length for each escalation signal.'''
    }
    {
      name: clear_intr_cnt_cg
      desc: '''Covers interrupt counter being cleared by class_clr_shadowed register.'''
    }
    {
      name: clear_esc_cnt_cg
      desc: '''Covers escalation counter being cleared by class_clr_shadowed register.'''
    }
    {
      name: alert_cause_cg
      desc: '''Covers alert_cause register and related items.

            - Collect which alert causes the alert_cause register to set.
            - Collect the alert_class that this alert belongs to.
            - Cross the above coverpoints.
            '''
    }
    {
      name: alert_loc_alert_cause_cg
      desc: '''Covers loc_alert_cause register regarding alert.

            - Collect two loc_alert causes: alert_ping_fail and alert_integrity_fail.
            - Collect which alert triggers this loc_alert.
            - Collect the alert_class that this local alert belongs to.
            - Cross the first coverpoint with the rest of the coverpoints.
            '''
    }
    {
      name: esc_loc_alert_cause_cg
      desc: '''Covers loc_alert_cause register regarding escalation.

            - Collect two loc_alert causes: esc_ping_fail and esc_integrity_fail.
            - Collect which escalation triggers this loc_alert.
            - Collect the alert_class that this local alert belongs to.
            - Cross the first coverpoint with the rest of the coverpoints.
            '''
    }
    {
      name: crashdump_trigger_cg
      desc: '''Covers which phase triggers crashdump.'''
    }
    {
      name: alert_en_regwen_cg
      desc: '''Covers if regwen is locked for alert_en registers.'''
    }
    {
      name: alert_class_regwen_cg
      desc: '''Covers if regwen is locked for alert_class registers.'''
    }
    {
      name: loc_alert_en_regwen_cg
      desc: '''Covers if regwen is locked for loc_alert_en registers.'''
    }
    {
      name: loc_alert_class_regwen_cg
      desc: '''Covers if regwen is locked for loc_alert_class registers.'''
    }
    {
      name: class_ctrl_regwen_cg
      desc: '''Covers if regwen is locked for class_ctrl registers.'''
    }
    {
      name: class_clr_regwen_cg
      desc: '''Covers if regwen is locked for class_clr registers.'''
    }
    {
      name: class_accum_thresh_regwen_cg
      desc: '''Covers if regwen is locked for class_accum_thresh registers.'''
    }
    {
      name: class_timeout_cyc_regwen_cg
      desc: '''Covers if regwen is locked for class_timeout_cyc registers.'''
    }
    {
      name: class_crashdump_trigger_regwen_cg
      desc: '''Covers if regwen is locked for class_crashdump_trigger registers.'''
    }
    {
      name: class_phase_cyc_regwen_cg
      desc: '''Covers if regwen is locked for class_phase_cyc registers.'''
    }
    {
      name: num_edn_reqs_cg
      desc: '''Covers if simulation runs long enough to capture more than five EDN requests.'''
    }
    {
      name: num_checked_pings_cg
      desc: '''Covers if simulation runs long enough to capture more than twenty ping requests.'''
    }
    {
      name: cycles_bwtween_pings_cg
      desc: '''Covers how many cycles are there between two ping requests.'''
    }
    {
      name: alert_ping_with_lpg_wrap_cg
      desc: '''Covers ping requests are initiated with LPG enabled or disabled.'''
    }

  ]
}
