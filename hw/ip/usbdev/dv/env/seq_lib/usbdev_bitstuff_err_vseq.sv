// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_bitstuff_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_bitstuff_err_vseq)

  `uvm_object_new

  task body();
    int unsigned sel = $urandom_range(0, 3);
    byte unsigned data[$];
    bit bitstuff_err;

    // See `usb20_agent_cfg.sv` for explanation => ensure that the bits after the bit stuffing
    // violation cannot constitute a valid SYNC signal.
    if (cfg.m_usb20_agent_cfg.rtl_limited_bitstuff_recovery) begin
      // Avoid the generation of randomized DATA packets because even if we control the content
      // after the bit stuffing violation we still cannot control the CRC16.
      //
      // Additionally, the DUT presently does not detect a bit suffing violation that occurs
      // immediately before the EOP (6 '1's should be followed by a stuffed '0' before EOP),
      // so ensure that the endpoint has its MSB clear.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ep_default, ep_default < 8;)
      sel = sel & 1;  // We can only exercise cases 0 and 1.
    end

    configure_out_trans(ep_default);
    // Enable the bitstuff error interrupt.
    csr_wr(.ptr(ral.intr_enable.rx_bitstuff_err), .value(1'b1));

    case (sel)
      0: begin
        // We need a known payload to guarantee a bit stuffing violation, and 6 contiguous
        // '1's shall be followed by a '0'...ie. 7 or more is a violation.
        data.push_back(8'hf0);  // LSB transmitted first...
        data.push_back(8'h07);  // ... so this supplies just 7 contiguous 1 bits.
      end
      1: begin
        // Contiguous run of '1's involving the device address and endpoint
        dev_addr = 7'h78;  // LSB transmitted first...
        ep_default = 4'h7;  // ... so this supplies just 7 contiguous '1's.
      end
      2: begin
        // Endpoint and CRC5; the final bit of the endpoint, combined with the 5 bits of the
        // CRC5 constitute a series of 6 but we can't emit 7 '1's and thus violate bit stuffing
        // without choosing an unimplemented endpoint.
        //
        // This OUT data packet will not be stored by the DUT but it does still report the
        // detection of bit stuffing violations in the packet before dropping it.
        dev_addr = 7'h7d;
        ep_default = 4'hf;
      end
      default: begin
        // Generate a random length packet of random data, and then set 7 bits at a random
        // position. We thus require a packet length of at least 1 byte in this case.
        build_prnd_bitstuff_packet(data);
      end
    endcase

    // Disable the bit stuffing logic in the driver.
    cfg.m_usb20_agent_cfg.disable_bitstuffing = 1'b1;

    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 0)
    csr_rd(.ptr(ral.intr_state.rx_bitstuff_err), .value(bitstuff_err));
    `DV_CHECK_EQ(bitstuff_err, 0)

    send_token_packet(ep_default, PidTypeOutToken);
    inter_packet_delay();
    send_data_packet(PidTypeData0, data);

    // All of these packets should be ignored, so we expect no response.
    check_no_response();

    // Re-enable the bit stuffing logic in the driver.
    cfg.m_usb20_agent_cfg.disable_bitstuffing = 1'b0;

    // Check that the bit stuffing violation was reported.
    csr_rd(.ptr(ral.intr_state.rx_bitstuff_err), .value(bitstuff_err));
    `DV_CHECK_EQ(bitstuff_err, 1)
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 1)

    // Clear the interrupt
    csr_wr(.ptr(ral.intr_state.rx_bitstuff_err), .value(1'b1));
    csr_wr(.ptr(ral.intr_enable.rx_bitstuff_err), .value(1'b0));
    loopback_delay();
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 0)
  endtask
endclass : usbdev_bitstuff_err_vseq
