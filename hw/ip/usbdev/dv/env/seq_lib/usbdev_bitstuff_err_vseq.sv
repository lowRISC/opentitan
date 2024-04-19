// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_bitstuff_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_bitstuff_err_vseq)

  `uvm_object_new

  task body();
    byte unsigned data[$];
    bit bitstuff_err;
    configure_out_trans();
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
        endp = 4'h7;  // ... so this supplies just 7 contiguous '1's.
      end
      2: begin
        // Endpoint and CRC5; the final bit of the endpoint, combined with the 5 bits of the
        // CRC5 constitute a series of 6 but we can't emit 7 '1's and thus violate bit stuffing
        // without choosing an unimplemented endpoint.
        //
        // This OUT data packet will not be stored by the DUT but it does still report the
        // detection of bit stuffing violations in the packet before dropping it.
        dev_addr = 7'h7d;
        endp = 4'hf;
      end
      default: begin
        // Generate a random length packet of random data, and then set 7 bits at a random
        // position. We thus require a packet length of at least 1 byte in this case.
        //
        // The aim here is to exercise all alignments w.r.t. byte boundaries.
        uint len = $urandom_range(1, MaxPktSizeByte) * 8;
        uint start = $urandom_range(0, len - 7);
        bit bit_data[$];
        for (uint b = 0; b < len; b++) begin
          bit_data.push_back((b >= start && b - start < 8) | ($urandom() & 1));
        end
        `uvm_info(`gfn, $sformatf("start %d len %d", start, len), UVM_DEBUG)
        `uvm_info(`gfn, $sformatf("bit_data %p", bit_data), UVM_DEBUG)
        // We need to ensure that the contiguous run of '1's is in the MSBs of the first byte
        // transmitted and the ensuing LSBs of the subsequent byte if it spans a byte boundary.
        data = {<<8{bit_data}};
        `uvm_info(`gfn, $sformatf("data %p", data), UVM_DEBUG)
      end
    endcase

    // Disable the bit stuffing logic in the driver.
    cfg.m_usb20_agent_cfg.disable_bitstuffing = 1'b1;

    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxBitstuffErr], 0)
    send_data_packet(PidTypeData0, data);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);

    // All of these packets should be ignored, so we expect no response.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.timed_out, 1);

    // Check that the bit stuffing violation was reported.
    csr_rd(.ptr(ral.intr_state.rx_bitstuff_err), .value(bitstuff_err));
    `DV_CHECK_EQ(1, bitstuff_err);
  endtask
endclass : usbdev_bitstuff_err_vseq
