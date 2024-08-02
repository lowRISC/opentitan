// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Suspend signaling (> 3ms of Idle state) is detected when Powered and when Active; exercise
// both of these transitions. Bus Reset is also detected in a number of states so test the DUT
// response whilst the device is in (i) Powered, (ii) PoweredSuspended, (iii) Active or
// (iv) Suspended.
class usbdev_link_suspend_vseq extends usbdev_pkt_sent_vseq;
  `uvm_object_utils(usbdev_link_suspend_vseq)

  `uvm_object_new

  // Generate traffic at the start of the test?
  rand bit gen_traffic;

  // Generate a Bus Reset when not (yet) Suspended?
  rand bit gen_reset_not_suspended;

  // Generate a Bus Reset when ..Suspended?
  rand bit gen_reset_suspended;

  // Duration of Bus Reset Signaling in microseconds.
  rand uint link_bus_reset_usecs;

  // More than about 3-4 microseconds should be enough from the perspective of the DUT, so keep it
  // short to check that brief assertions are not missed, but 4 runs the risk of sampling issues
  // since the DUT has an internal microsecond ticker of arbitrary phase relationship.
  constraint link_bus_reset_usecs_c {
    link_bus_reset_usecs > 4 && link_bus_reset_usecs < 10;
  }

  rand uint link_rst_suspend_clks;

  // Section 7.1.7.6 of the USB 2.0 Protocol Specification
  // - more than 3.0ms of constant Idle signaling shall put the device in
  //   Suspend state.
  constraint link_rst_suspend_clks_c {
    link_rst_suspend_clks >= 3_100 * 48 &&  // 3.1ms in 48MHz clock cycles.
    link_rst_suspend_clks <= 6_200 * 48;    // There's no real upper bound; just simulation time.
  }

  // Delay between SOF packets in 48MHz clock cycles.
  //  (Start Of Frame packets are 1ms apart, and 32 bits in duration like other token packets.)
  uint inter_sof_delay_clks = 1_000 * 48 - (32 * 4);  // 4 times oversampling per bit.

  // Configure, run and suspend the DUT; this task is called by derived sequences.
  task run_and_suspend();
    // Declare our choices.
    `uvm_info(`gfn, $sformatf("Traffic %0d reset_not_suspended %0d reset_suspended %0d",
                              gen_traffic, gen_reset_not_suspended, gen_reset_suspended), UVM_LOW)

    if (gen_traffic) begin
      // Send transaction to make link active
      super.body();

      // Read USB status to check link is active
      // Link state should be active no SOF
      wait_for_link_state({LinkActiveNoSOF}, .timeout_clks(4), .fatal(1));

      // Generate a few Start Of Frame packets.
      repeat (5) begin
        send_sof_packet(PidTypeSofToken);
        cfg.clk_rst_vif.wait_clks(inter_sof_delay_clks);
      end

      // The link should now be active.
      wait_for_link_state({LinkActive}, .timeout_clks(4), .fatal(1));
    end else begin
      // At this point the DUT may have perceived the pre-VBUS assertion condition of DP/DN both low
      // as a Bus Reset, and we must avoid a rapid transition through the `Powered` state into
      // `ActiveNoSOF` since there is no direct way to return to `Powered`.
      //
      // We can achieve this by disconnecting again for a short while, but not more than the ca. 4us
      // required for the DUT to perceive another Bus Reset.
      usbdev_disconnect();
      usbdev_connect();

      // Check that we've moved into the Powered state; link state should be almost immediate.
      wait_for_link_state({LinkPowered}, .timeout_clks(4), .fatal(1));
    end

    // Ensure the interrupt is not presently asserted.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkSuspend));

    // Shall we try generating a Bus Reset from the `Powered`/`Active` state?
    if (gen_reset_not_suspended) begin
      send_bus_reset(link_bus_reset_usecs);

      // Either should transition us to `ActiveNoSOF` because the USB link is now up but we have not
      // yet received a Start Of Frame packet. Bus Reset signal is filtered, so propagation is a
      // little slower than other link state changes in this sequence.
      wait_for_link_state({LinkActiveNoSOF}, .timeout_clks(12), .fatal(1));

      // The USB link is now up and ready for traffic following the Bus Reset, so the DUT is
      // expected to move to `Suspended` and not `PoweredSuspended` when we leave the bus Idle.
      gen_traffic = 1'b1;
    end

    // Wait for longer than 3ms, generating no activity; bus remains Idle.
    cfg.clk_rst_vif.wait_clks(link_rst_suspend_clks);

    // The DUT should have transitioned into either `Suspended` or `PoweredSuspended` depending on
    // its previous state.
    if (gen_traffic) begin
      wait_for_link_state({LinkSuspended}, .timeout_clks(4), .fatal(1));
    end else begin
      wait_for_link_state({LinkPoweredSuspended}, .timeout_clks(4), .fatal(1));
    end

    // Check that the link suspend interrupt has been asserted.
    wait_for_interrupt(1 << IntrLinkSuspend, .timeout_clks(1), .clear(1), .enforce(1));
    // Disable the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
  endtask

  task body();
    run_and_suspend();

    // Shall we try generating a Bus Reset from the `(Powered)Suspended` state?
    if (gen_reset_suspended) begin
      send_bus_reset(link_bus_reset_usecs);

      // Whether or not we generated any traffic the DUT should be in `ActiveNoSOF` following a
      // bus reset, because the bus will be Idle and no SOF packets have yet been received.
      // Bus Reset is filtered so propagation is a little slower.
      wait_for_link_state({LinkActiveNoSOF}, .timeout_clks(12), .fatal(1));
    end

    // Disconnect us from the USB by removing the pullup; the link state change should be almost
    // immediate.
    usbdev_disconnect();
    wait_for_link_state({LinkDisconnected}, .timeout_clks(4), .fatal(1));

    // Disconnect VBUS too and we're done.
    set_vbus_state(0);
  endtask
endclass : usbdev_link_suspend_vseq
