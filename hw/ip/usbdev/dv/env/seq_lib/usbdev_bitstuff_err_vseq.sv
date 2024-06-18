// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_bitstuff_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_bitstuff_err_vseq)

  `uvm_object_new

  task body();
    byte unsigned data[$];
    bit bitstuff_err;
    configure_out_trans(ep_default);
    case ($urandom_range(0,3))
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

    send_token_packet(ep_default, PidTypeOutToken);
    inter_packet_delay();
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 0)
    send_data_packet(PidTypeData0, data);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);

    // All of these packets should be ignored, so we expect no response.
    `DV_CHECK_EQ(m_usb20_item.timed_out, 1);

    // Check that the bit stuffing violation was reported.
    csr_rd(.ptr(ral.intr_state.rx_bitstuff_err), .value(bitstuff_err));
    `DV_CHECK_EQ(1, bitstuff_err);
  endtask
endclass : usbdev_bitstuff_err_vseq
