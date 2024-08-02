// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_link_resume test vseq
class usbdev_link_resume_vseq extends usbdev_link_suspend_vseq;
  `uvm_object_utils(usbdev_link_resume_vseq)

  `uvm_object_new

  rand int unsigned link_resume_duration_usecs;

  // Resume Signaling should be at least 20ms according to the protocol specification; there's
  // really no need for that in simulation every time, though. Just make sure that it's covered.
  constraint link_resume_duration_usecs_c {
    (link_resume_duration_usecs >=  1_000 && link_resume_duration_usecs <  5_000) ||
    (link_resume_duration_usecs >= 18_000 && link_resume_duration_usecs < 24_000);
  }

  // Check the assertion of the interrupt to indicate the presence of Resume Signaling; since the
  // timing of this varies with whether we were active previously or just powered up, do it in
  // parallel with the Resume Signaling itself.
  task check_interrupt();
    uvm_reg_data_t link_state;
    csr_rd(.ptr(ral.usbstat.link_state), .value(link_state));
    case (link_state)
      LinkSuspended, LinkResuming: begin
        // If we're `Suspended` having being active, the interrupt should be asserted at the end of
        // Resume Signaling to inform software.
        wait_for_link_state({LinkActiveNoSOF}, .timeout_clks(link_resume_duration_usecs * 48),
                            .fatal(1));
      end
      LinkPoweredSuspended, LinkPowered: begin
        // If we're resuming having not been active since we powered up (return from Deep Sleep),
        // the interrupt should occur immediately upon detection of Resume Signaling, to give the
        // software time to reinstate the configuration and prepare for communication.
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected link state 0x%0x", link_state))
    endcase

    // The interrupt should now have become asserted.
    wait_for_interrupt(1 << IntrLinkResume, .timeout_clks(8), .clear(0), .enforce(1));
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkResume], 1'b1, "Interrupt line not asserted")

    // If we were powered down then the DUT needs a nudge from software at this point before it
    // will proceed to ActiveNoSOF.
    if (link_state inside {LinkPoweredSuspended, LinkPowered}) begin
      // Now prod the DUT into the Resuming state, which should be essentially immediate.
      ral.usbctrl.resume_link_active.set(1'b1);
      csr_update(ral.usbctrl);
      wait_for_link_state({LinkResuming}, .timeout_clks(4), .fatal(1));
    end
  endtask

  task body();
    // Send transaction to make link active
    run_and_suspend();

    // Check that the DUT is presently (Powered)Suspended.
    wait_for_link_state({LinkSuspended, LinkPoweredSuspended}, .timeout_clks(1), .fatal(1));

    // Ensure the interrupt is not presently asserted, and then enable it.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkResume));
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrLinkResume));
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkResume], 1'b0, "Interrupt line should not be asserted")

    fork
      // Ask the driver to Resume the DUT; Resume Signaling should be >= 20ms.
      send_resume_signaling(link_resume_duration_usecs);
      // Check for the assertion of the `link_resume` interrupt.
      check_interrupt();
    join

    // The USB should also be back in the Idle state, with no SOF having yet been transmitted.
    wait_for_link_state({LinkActiveNoSOF}, .timeout_clks(4), .fatal(1));

    // Disable and clear the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkResume));

    // Disconnect us from the USB by removing the pullup; the link state change should be almost
    // immediate.
    usbdev_disconnect();
    wait_for_link_state({LinkDisconnected}, .timeout_clks(4), .fatal(1));

    // Disconnect VBUS too and we're done.
    set_vbus_state(0);
  endtask
endclass : usbdev_link_resume_vseq
