// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_tx_osc_test_mode_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_config_tx_osc_test_mode_vseq)

  `uvm_object_new

  // This should put the DUT in a mode where it emits the TX OSC on the DP/DN pins, toggling them
  // in anti-phase, at 12Mbps:
  //         ___     ___     ___     ___     __
  // DP  ___/   \___/   \___/   \___/   \___/
  //     ___     ___     ___     ___     ___
  // DN     \___/   \___/   \___/   \___/   \__
  //
  // Since these are output signals without a CDC we may rely upon them being exactly synchronized.
  // Each high/low or low/high state is referred to as a 'phase' throughout.

  task pre_start();
    // Prevent normal device initialization.
    //
    // This sequence is designed to drive the USB lines without valid USB traffic, so the
    // last thing we need is the driver and monitor connecting. The monitor would reject the bus
    // state or apparent traffic.
    do_usbdev_init = 1'b0;

    super.pre_start();
  endtask

  // Sample the DP/DN signals of the USB.
  task sample_signals(output bit dp, output bit dn);
    // Sample the new state of the signals using the 48MHz DUT clock; direct signal access is less
    // than ideal but we can't feasibly sample DP/DN using CSR reads because reading is too slow.
    cfg.clk_rst_vif.wait_clks(1);
    dp = cfg.m_usb20_agent_cfg.bif.usb_p;
    dn = cfg.m_usb20_agent_cfg.bif.usb_n;
  endtask

  task body();
    // A fairly arbitrary choice; a compromise between test duration and accuracy of the mean.
    int unsigned num_phases = 2_000;
    // Total number of samples measured across all phases.
    int unsigned total_duration = 0;
    // Number of samples measured within this phase of TX oscillation.
    int unsigned phase_duration = 0;
    // Current phase number.
    int unsigned phase = 0;
    bit prev_dp, prev_dn;
    bit dp, dn;

    // For the TX OSC test mode to work, the bus must not be in reset.
    set_vbus_state(1);
    // Instruct the driver to perform Bus Reset Signaling; keep this to 100us since there's no
    // point wasting simulation time on all sequences. Full length resets are exercised in
    // usbdev_bus_rand_vseq.
    send_bus_reset(100);

    // Enable TX OSC test mode.
    csr_wr(.ptr(ral.phy_config.tx_osc_test_mode), .value(1'b1));

    // It can take up to 1 byte transmission time for the oscillator to start transmitting;
    // this is 4 x 8 clock cycles, but allow a little extra for internal DUT propagation.
    cfg.clk_rst_vif.wait_clks(44);

    // Collect the initial values.
    sample_signals(prev_dp, prev_dn);

    // Check that the DP and DN signals are driven out-of-phase and with the expected frequency.
    while (phase < num_phases) begin
      phase_duration++;
      sample_signals(dp, dn);

      `uvm_info(`gfn, $sformatf("Sampled DP %d and DN %d", dp, dn), UVM_HIGH)
      `DV_CHECK_EQ(dp, !dn, "DP and DN should be opposites")

      if (dp == prev_dp) begin
        `DV_CHECK_LT(phase_duration, 8, "Phase too long; check osc frequency")
      end else begin
        `uvm_info(`gfn, $sformatf("Phase %d has duration %d, total = %d", phase, phase_duration,
                                  total_duration), UVM_HIGH)
        // We're sampling a 12Mbps stream on our 48MHz clock and, although the sampling phase is
        // unknown in principle, in simulation it will be fixed; don't check the first phase
        // because we could start sampling anywhere within it.
        `DV_CHECK(!phase || (phase_duration >= 3 && phase_duration <= 5),
                  $sformatf("Unexpected phase duration %d", phase_duration))
        total_duration += phase_duration;
        // Advance to next phase.
        phase_duration = 0;
        prev_dp = dp;
        phase++;
      end
    end

    // Check the mean phase duration; expect to see 4 cycles for each phase, allow a little error
    // for sampling phase issues.
    `DV_CHECK(total_duration >= 4 * (num_phases - 1) && total_duration <= 4 * (num_phases + 1),
              "Average phase duration is unexpected; check osc frequency")
  endtask
endclass
