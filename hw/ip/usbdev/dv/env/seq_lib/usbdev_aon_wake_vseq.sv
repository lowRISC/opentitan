// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic test of AON/Wake module functionality.
class usbdev_aon_wake_vseq extends usbdev_link_suspend_vseq;
  `uvm_object_utils(usbdev_aon_wake_vseq)

  `uvm_object_new

  // Delay before producing stimulus to AON/Wake module.
  rand int stim_delay_clks;
  constraint stim_delay_clks_c {
    // Weighted to make 'no delay' a more frequent occurrence,
    // by treating all negative values as per zero.
    stim_delay_clks >= -50 && stim_delay_clks <= 2000;
  }

  // Delay before optional reconnection of VBUS after disconnection.
  rand int disconn_interval_clks;
  constraint disconn_interval_clks_c {
    // In practice the DUT will have capacitance on the VBUS line to stabilize it and to ignore
    // transients. Additionally, the AON/Wake module operates on a much lower clock frequency than
    // the DUT, so glitches will (deliberately) be filtered out.
    //
    // We therefore need to make the VBUS removal long enough to be detected.
    disconn_interval_clks >= 2000 && disconn_interval_clks <= 50000;
  }

  // Attempt to modify the pull-up enables whilst AON/Wake is activated?
  rand bit perturb_enables;

  // Attempt to disrupt the USB pull-up enables
  // (any changes that we make should not be visible on the USB when the AON/Wake module has
  //  control).
  task attempted_change();
    bit pullup_maintained = $urandom & 1;
    bit flip_pins = $urandom & 1;
    ral.usbctrl.enable.set(pullup_maintained);
    csr_update(.csr(ral.usbctrl));
    ral.phy_config.pinflip.set(flip_pins);
    csr_update(.csr(ral.phy_config));
    `uvm_info(`gfn, $sformatf("Attempted to set enable %d flip pins %d",
                              pullup_maintained, flip_pins), UVM_HIGH)
  endtask

  task body();
    bit exp_dp_pullup, exp_dn_pullup;
    uvm_reg_data_t wake_events;
    int delay_clks;

    // Set up the DUT, do some minimal traffic and then check that the USBDEV has detected
    // and reported that it has been Suspended; `usbdev_link_suspend_vseq` supplies the
    // Suspend signaling.
    super.body();

    // Report configuration.
    `uvm_info(`gfn, $sformatf("do_resume_signaling %d do_reset_signaling %d do_vbus_disconnects %d",
                              do_resume_signaling, do_reset_signaling, do_vbus_disconnects),
              UVM_MEDIUM)
    // `usbdev_base_vseq` shall collect bus stimuli to be provided; just check here that we've been
    // asked for only one.
    `DV_CHECK_EQ(32'(do_resume_signaling) + 32'(do_reset_signaling) + 32'(do_vbus_disconnects), 1)

    // Hand over control of the USB to the `usbdev_aon_wake` module
    // TODO: we ought to try to overlap the stimulus and the AON/Wake activation.
    aon_wake_activate();

    // Expected state of pull-up enables after deactivating the AON/Wake module later.
    exp_dp_pullup = !phy_pinflip;
    exp_dn_pullup =  phy_pinflip;

    // AON/Wake module should now have control of the USB pull ups; try to break things
    // (but not in every case because doing so introduces a delay and we must test
    //  immediate stimuli too)...
    if (perturb_enables) attempted_change();

    // Just introduce a small variable delay before we send the test stimulus.
    if (stim_delay_clks > 0) begin
      cfg.clk_rst_vif.wait_clks(stim_delay_clks);
    end

    // Produce the appropriate stimulus; only one shall have been requested (see above).
    casez ({do_resume_signaling, do_reset_signaling, do_vbus_disconnects})
      3'b1??:  send_resume_signaling();
      3'b01?:  send_bus_reset();
      default: begin
        set_vbus_state(0);
        // Decide whether to reconnect the VBUS; a fairly brief interruption should also be
        // detected and reported, but glitches are intended to be ignored.
        cfg.clk_rst_vif.wait_clks(disconn_interval_clks);
        if ($urandom & 1) begin
          set_vbus_state(1);
          // Another short delay to check that reinstating VBUS does not clear the wake request
          // and/or reported event.
          cfg.clk_rst_vif.wait_clks($urandom_range(1, 2000));

          // TODO: Draft PR #19270 contends that perhaps this is undesirable behavior, but the
          // pull-up presently will be re-enabled if VBUS is reinstated. Firmware may detect and
          // prevent this if required.
        end else begin
          // If VBUS remains deasserted, the pull-up enable shall remain deasserted by the DUT too.
          if (phy_pinflip) exp_dn_pullup = 1'b0;
          else exp_dp_pullup = 1'b0;
        end
      end
    endcase

    // AON/Wake module filters the input stimuli to provide some protection against transients;
    // - the CDC signals may be 3 cycles, filtering another 4 and then a couple of register delays
    //   until the new state information is presented in the DUT via the CSRs.
    // - there is also CDC crossing back to the 48MHz clock, so allow 12 cycles total.
    cfg.aon_clk_rst_vif.wait_clks(12);

    // Check that the AON/Wake module has signaled the 'Wake up' request (this would normally go
    // to the power management within the SoC).
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.wake_req_aon, 1'b1, "Wake up request not detected")

    // Check the event report from the AON/Wake module; we should see only the stimulus that we
    // supplied.
    csr_rd(.ptr(ral.wake_events), .value(wake_events));
    `uvm_info(`gfn, $sformatf("Wake events returned as 0x%x", wake_events), UVM_MEDIUM)

    `DV_CHECK_EQ(get_field_val(ral.wake_events.module_active, wake_events), 1'b1)
    `DV_CHECK_EQ(get_field_val(ral.wake_events.disconnected, wake_events), do_vbus_disconnects)
    `DV_CHECK_EQ(get_field_val(ral.wake_events.bus_reset, wake_events), do_reset_signaling)
    // Note that a Bus Reset also constitutes 'Bus not idle' because it's not 'J/Idle' state.
    `DV_CHECK_EQ(get_field_val(ral.wake_events.bus_not_idle, wake_events),
                 do_resume_signaling | do_reset_signaling)

    // The DUT (USBDEV) should not have control of the pull up enables at this point; our efforts
    // at breaking things above should have been unsuccessful.
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dp_pullup_o, !phy_pinflip,
                      "DP pull up not as expected with AON/Wake module active")
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dn_pullup_o,  phy_pinflip,
                      "DN pull up not as expected with AON/Wake module active")

    // Reinstate our pull up enable.
    ral.usbctrl.enable.set(1'b1);
    csr_update(.csr(ral.usbctrl));
    ral.phy_config.pinflip.set(1'b0);
    csr_update(.csr(ral.phy_config));

    // Instruct the AON/Wake module to hand back control of the USB.
    aon_wake_deactivate();

    // Check that the 'wake up' request has been removed.
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.wake_req_aon, 1'b0, "Wake up request not removed")

    // USBDEV should once again have control of the pull-up enables.
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dp_pullup_o, exp_dp_pullup,
                      "DP pull up was not returned")
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dn_pullup_o, exp_dn_pullup,
                      "DN pull up was not returned")

    usbdev_disconnect();

    // Check that the USBDEV has disconnected successfully.
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dp_pullup_o, 1'b0,
                      "DP pull up was not released")
    `DV_CHECK_CASE_EQ(cfg.m_usb20_agent_cfg.bif.usb_dn_pullup_o, 1'b0,
                      "DN pull up was not released")
  endtask
endclass : usbdev_aon_wake_vseq
