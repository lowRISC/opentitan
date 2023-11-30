// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_packetiser class
// -------------------------------
class usbdev_packetiser extends uvm_object;
  `uvm_object_utils(usbdev_packetiser)

  // These arrays contains respective packets.
  bit token_pkt_arr[];
  bit data_pkt_arr[];
  bit handshake_pkt_arr[];

  // Handles to usb20_item and classes derived from usb20_item
  usb20_item     m_usb20_item;
  token_pkt      m_tpkt;
  data_pkt       m_dpkt;
  handshake_pkt  m_hpkt;

  function new(string name = "usbdev_packetiser");
    super.new(name);
    m_usb20_item = new("usb20_item");
    m_tpkt       = new("token_pkt");
    m_dpkt       = new("data_pkt");
    m_hpkt       = new("handshake_pkt");
  endfunction

  // pack_pkt task
  // -------------------------------
  task pack_pkt();
    if (m_usb20_item.m_pkt_type == PktTypeToken) begin
      m_tpkt.pack(token_pkt_arr);
    end
    else if (m_usb20_item.m_pkt_type == PktTypeData) begin
      m_dpkt.pack(data_pkt_arr);
    end
    else if (m_usb20_item.m_pkt_type == PktTypeHandshake) begin
      m_hpkt.pack(handshake_pkt_arr);
    end
    else;
  endtask
endclass
