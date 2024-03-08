// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_out_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_iso_vseq)

  `uvm_object_new

  task body();
    // Expected data content of packet
    byte unsigned exp_data[];
    bit pkt_received;
    configure_out_trans();
    // ISO EP OUT
    csr_wr(.ptr(ral.out_iso[0].iso[endp]), .value(1'b1));
    // write to clear pkt_received interrupt. Verify this after transaction.
    csr_wr(.ptr(ral.intr_state.pkt_received), .value(1'b1));
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(64),
                  .isochronous_transfer(1'b1));
    // Wait until usbdev generates an interrupt to show the packet has been received. This should
    // happen without needing an ACK from the host because the device is configured for ISO traffic.
    for (int i = 0; i < 10; i++) begin
      csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
      if (pkt_received) break;
    end
    if (!pkt_received) begin
      `uvm_error(`gfn, "usbdev didn't generate expected pkt_received interrupt")
    end
    // verify that after OUT Iso device ports is on IDLE J statmeans not sending any ACK pkt.
    check_device_status();
    check_rx_packet(endp, 1'b0, out_buffer_id, m_data_pkt.data);
  endtask

  task check_device_status();
    for (int i=0; i < 18; i++) begin
      bit prev_usb_p;
      bit prev_usb_n;
      @(posedge cfg.m_usb20_agent_cfg.bif.usb_clk);
      if (cfg.m_usb20_agent_cfg.bif.usb_p != prev_usb_p &&
          cfg.m_usb20_agent_cfg.bif.usb_n != prev_usb_n) begin
        `uvm_error(`gfn, "usbdev is not Idle") break;
      end
        prev_usb_p = cfg.m_usb20_agent_cfg.bif.usb_p;
        prev_usb_p = cfg.m_usb20_agent_cfg.bif.usb_p;
    end
  endtask
endclass
