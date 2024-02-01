// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_transaction_manager extends uvm_object;
  `uvm_object_utils(usbdev_transaction_manager)

  usbdev_packetiser m_usbdev_packetiser;
  usbdev_packet_classifier m_usbdev_packet_classifier;
  usbdev_data_integrity  m_usbdev_data_integrity;
  usb20_item m_usb20_item;
  token_packet m_token_pkt;
  data_packet m_data_pkt;
  hand_shake_packet m_handshake_pkt;
  usbdev_handshake_pkt_e m_usbdev_handshake_pkt;
  usb_transfer_e m_usb_transfer;

  logic [1:0] state;
  logic [6:0] address;
  logic [3:0] endpoint;
  bit data[];
  bit [7:0] pid;

  function new(string name  = "usbdev_transaction_manager");
    super.new(name);
    m_usbdev_packetiser = new();
    m_usbdev_packet_classifier = new();
    m_usbdev_data_integrity = new();
    m_token_pkt = new();
    m_data_pkt = new();
    m_handshake_pkt = new();
    m_usb20_item = new();
    state = 2'b0;
    pid = 8'b0;
    address = 7'b0;
    endpoint = 4'b0;
  endfunction

  task transaction_manager(input bit t_pkt[], input bit d_pkt[], input bit h_pkt[]);
    m_usbdev_packet_classifier.checkPacket(t_pkt);
    if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_SETUP) begin
      setup_transaction(d_pkt, h_pkt);
    end
    if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_IN) begin
      in_transaction(d_pkt, h_pkt);
    end
    if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_OUT) begin
      out_transaction(d_pkt, h_pkt);
    end
  endtask

  task setup_transaction(input bit d_pkt[], input bit h_pkt[]);
    case (state)
      0 : begin
        if (m_usbdev_packet_classifier.pid == PidTypeSetupToken) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid, address, endpoint);
          state = 1;
        end
      end
      1 : begin
        m_usbdev_packet_classifier.checkPacket(d_pkt);
        if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_0) begin
          pid = m_usbdev_packet_classifier.pid;
          data = m_usbdev_packet_classifier.data;
          m_data_pkt.send_data_packet(pid, data);
          m_usbdev_data_integrity.write(pid,address ,endpoint, data);
          state = 2;
        end
      end
      2 : begin
        if (m_usbdev_handshake_pkt == ACK) begin
          m_usb20_item.m_pid_type = PidTypeAck;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end else if (m_usbdev_handshake_pkt == NAK) begin
          m_usb20_item.m_pid_type = PidTypeNak;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end else if (m_usbdev_handshake_pkt == STALL) begin
          m_usb20_item.m_pid_type = PidTypeStall;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end
      end
       default : state = 0;
    endcase
  endtask

  task in_transaction(input bit d_pkt[], input bit h_pkt[]);
    case (state)
      0 : begin // Address and endpoint sent to data_integrity
        if (m_usbdev_packet_classifier.pid == PidTypeInToken) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid, address, endpoint);
          if (m_usbdev_handshake_pkt == STALL) begin
            m_usbdev_packet_classifier.pid = PidTypeStall;
            pid = m_usbdev_packet_classifier.pid;
            m_handshake_pkt.send_handshake_packet(pid);
            state = 0;
          end
          else state = 1;
        end
      end
      1 : begin // Getting data from data integrity
        m_usbdev_data_integrity.read(pid, address, endpoint, data);
        m_data_pkt.send_data_packet(pid, data);
        if (m_usb_transfer == IsoTrans)
          state = 0;
        else state = 2;
      end
      2 : begin
        m_usbdev_packet_classifier.checkPacket(h_pkt);
        if (m_usbdev_packet_classifier.pid == PidTypeAck) begin
          pid = m_usbdev_packet_classifier.pid;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end
        else if (m_usbdev_packet_classifier.pid == PidTypeNak) begin
          pid = m_usbdev_packet_classifier.pid;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end
        else if (m_usbdev_packet_classifier.pid == PidTypeStall) begin
          pid = m_usbdev_packet_classifier.pid;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end
      end
      default : state = 0;
    endcase
  endtask

  task out_transaction(input bit d_pkt[], input bit h_pkt[]);
    case(state)
      0 : begin
        if (m_usbdev_packet_classifier.pid == PidTypeOutToken) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid, address, endpoint);
          state = 1;
        end
      end
      1 : begin
        m_usbdev_packet_classifier.checkPacket(d_pkt);
        if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_0 ||
            m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_1) begin
          pid = m_usbdev_packet_classifier.pid;
          data = m_usbdev_packet_classifier.data;
          m_data_pkt.send_data_packet(pid, data);
          m_usbdev_data_integrity.write(pid, address, endpoint, data);
          if (m_usb_transfer == IsoTrans)
            state = 0;
          else state = 2;
        end
      end
      2 : begin
        if (m_usbdev_handshake_pkt == ACK) begin
          m_usb20_item.m_pid_type = PidTypeAck;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end else if (m_usbdev_handshake_pkt == NAK) begin
          m_usb20_item.m_pid_type = PidTypeNak;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end else if (m_usbdev_handshake_pkt == STALL) begin
          m_usb20_item.m_pid_type = PidTypeStall;
          pid = m_usb20_item.m_pid_type;
          m_handshake_pkt.send_handshake_packet(pid);
          state = 0;
        end
      end
      default : state = 0;
    endcase
  endtask
endclass
