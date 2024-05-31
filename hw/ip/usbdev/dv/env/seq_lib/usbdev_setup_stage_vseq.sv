// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_setup_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_stage_vseq)

  `uvm_object_new

  task body();
    // Configure setup transaction
    configure_setup_trans(ep_default);

    // -------------------------------------------------------------------------------------
    // SETUP token packet followed by a control DATA packet of 8 bytes
    // -------------------------------------------------------------------------------------
    send_token_packet(ep_default, PidTypeSetupToken);
    inter_packet_delay();
    call_desc_sequence(PidTypeData0);

    // Check that the packet was accepted (ACKnowledged) by the USB device.
    check_response_matches(PidTypeAck);
  endtask

  // Construct and transmit a DATA packet containing a SETUP descriptor to the USB device
  task call_desc_sequence(input pid_type_e pid_type);
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    start_item(m_data_pkt);
    m_data_pkt.m_ev_type  = EvPacket;
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = pid_type;
    // Send control data for GET_DESCRIPTOR request
    m_data_pkt.make_device_request(bmRequestType3, bRequestGET_DESCRIPTOR,
                                   8'h00, 8'h01, 16'h0, 16'd18);
    finish_item(m_data_pkt);
  endtask

endclass
