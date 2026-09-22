// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This should put the DUT in a mode where it transmits a packet repeatedly as if the
// USB Host Controller had requested an IN transaction from Endpoint Zero.
//
// It then monitors the USB signals directly, looking for inter-packet gaps (J/Idle),
// and EOP states.

class usbdev_phy_config_tx_pkt_test_mode_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_config_tx_pkt_test_mode_vseq)

  `uvm_object_new

  // Randomized IN data packet.
  rand byte unsigned pkt_data[];
  constraint pkt_data_size_c {
    pkt_data.size() <= MaxPktSizeByte;
  }

  task pre_start();
    // Prevent normal device initialization.
    //
    // This sequence is designed to drive the USB lines in a manner that is not compliant with
    // the USB Protocol Specification, so the last thing we need is the driver and monitor
    // connecting. The monitor would reject the bus state or apparent traffic.
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
    // Use the highest-numbered buffer; it's of no consequence which we use really but
    // configuration registers typically reset to zero.
    int unsigned buf_id = NumBuffers - 1;
    // Max duration of inter-packet gap; use 32 microseconds. The specification - though it
    // doesn't really apply to Full Speed - states 125 microseconds, but we expect the DUT
    // to exhibit a much shorter gap.
    int unsigned gap_max = 32 * 48;  // ca. 48MHz sampling.
    // A fairly arbitrary choice; a compromise between test duration and robustness.
    int unsigned num_packets = 200;
    // Number of samples of EOP state counted.
    int unsigned eop_duration = 0;
    // Number of samples measured within this inter-packet gap.
    int unsigned gap_duration = 0;
    // Current packet number.
    int unsigned packet = 0;
    int unsigned clk_wait;
    bit prev_dp, prev_dn;
    bit dp, dn;

    // For the TX PKT test mode to work, the bus must not be in reset.
    set_vbus_state(1);

    // Ensure that the DUT is driving the pull up enable because otherwise the logic will sit in
    // 'link reset' as both DP and DN are weakly pulled low by the host.
    usbdev_connect();

    // Instruct the driver to perform Bus Reset Signaling; keep this to 100us since there's no
    // point wasting simulation time on all sequences. Full length resets are exercised in
    // usbdev_bus_rand_vseq.
    send_bus_reset(100);

    // Configure an IN packet for collection from the DUT.
    write_buffer(buf_id, pkt_data);
    configure_in_trans(4'h0, buf_id, pkt_data.size());

    // Enable TX PKT test mode.
    csr_wr(.ptr(ral.phy_config.tx_pkt_test_mode), .value(1'b1));

    // It can take up to 1 byte transmission time for the DUT to start transmitting;
    // this is 4 x 8 clock cycles, but allow a little extra for internal DUT propagation.
    cfg.clk_rst_vif.wait_clks(44);

    // Collect the initial values.
    sample_signals(prev_dp, prev_dn);

    // Check that the DP and DN signals are observed to vary; since there is no stimulus from
    // the USB host controller, this means that the device is transmitting automatically.
    //
    // Rather than replicate all the complexity of packet decoding, we'll just count EOP states
    // and measure the inter-packet gaps. This test mode is not a part of normal operation,
    // nor a requirement of the USB Protocol Specification.
    while (packet < num_packets) begin
      sample_signals(dp, dn);
      `uvm_info(`gfn, $sformatf("Sampled DP %d and DN %d", dp, dn), UVM_HIGH)
      case ({dp, dn})
        // EOP state; measure the duration of the End Of Packet.
        2'b00: begin
          gap_duration = 0;
          eop_duration++;
          `DV_CHECK_LT(eop_duration, 16, "EOP signaling too long; check transmission")
        end
        // Idle state; measure the inter-packet gap.
        2'b10: begin
          if ({prev_dp, prev_dn} === 2'b00) begin
            `uvm_info(`gfn, $sformatf("End Of Packet %d detected", packet), UVM_LOW)
            packet++;
          end
          eop_duration = 0;
          gap_duration++;
          `DV_CHECK_LT(gap_duration, gap_max, "Inter-packet gap too long; check transmission")
        end
        2'b11: begin
          `dv_fatal("Invalid USB line state observed")
        end
        default: begin
          // This is packet transmission.
          eop_duration = 0;
          gap_duration = 0;
        end
      endcase
      {prev_dp, prev_dn} = {dp, dn};
    end

    // The DUT should exit this test mode in response to a VBUS disconnection; ask the driver
    // to drop VBUS after a randomized short delay. VBUS disconnection may occur at any point on
    // the physical system, so the DUT should be able to handle that and be usable afterwards.
    clk_wait = $urandom_range(pkt_data.size() * 8 * 4, 0);  // Anywhere within the packet.
    cfg.clk_rst_vif.wait_clks(clk_wait);
    set_vbus_state(1'b0);

    // Check that the TX Packet test mode has ended, very soon after VBUS has dropped but there
    // are short internal delays.
    loopback_delay();
    csr_rd_check(.ptr(ral.phy_config.tx_pkt_test_mode), .compare_value(1'b0),
                      .err_msg("DUT has not exited TX PKT test mode when expected"));
 endtask
endclass
