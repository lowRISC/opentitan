// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_out_data_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_data_stage_vseq)

  `uvm_object_new

  task body();

    configure_out_trans();
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_control_data_sequence();
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    // Check that the USB device respond with ACK or NAK
    case (m_usb20_item.m_pid_type)
      PidTypeAck: get_out_response_from_device(m_usb20_item, PidTypeAck);
      PidTypeNak: get_out_response_from_device(m_usb20_item, PidTypeNak);
      default: `uvm_error(`gfn, "Usbdev OUT Transaction Failed")
    endcase
    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, m_data_pkt.data);
  endtask

  // Construct and transmit a control data packet
  task call_control_data_sequence();
    `uvm_create_on(m_data_pkt, p_sequencer.usb20_sequencer_h)
    m_data_pkt.m_pkt_type = PktTypeData;
    m_data_pkt.m_pid_type = PidTypeData0;
    // Construct a GET DESCRIPTOR request that retrieves the Device descriptor
    m_data_pkt.m_bmRT = bmRequestType3;
    m_data_pkt.m_bR = bRequestGET_DESCRIPTOR;
    assert(m_data_pkt.randomize());
    m_data_pkt.make_device_request(m_data_pkt.m_bmRT, m_data_pkt.m_bR,
                                   8'h00, 8'h01, 16'h0, 16'd18);
    start_item(m_data_pkt);
    finish_item(m_data_pkt);
  endtask
endclass
