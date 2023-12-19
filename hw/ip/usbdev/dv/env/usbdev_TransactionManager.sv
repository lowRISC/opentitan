// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_TransactionManager extends uvm_object;
  `uvm_object_utils(usbdev_TransactionManager)

  usbdev_packetiser m_usbdev_packetiser;
  usbdev_packet_classifier m_usbdev_packet_classifier;
  usbdev_data_integrity  m_usbdev_data_integrity;
  token_packet      m_token_pkt;
  data_packet       m_data_pkt;
  hand_shake_packet m_handshake_pkt;
  logic [1:0]state;
  logic [6:0] address;
  logic [3:0] endpoint;
  bit data[];
  bit [7:0] pid;

  function new(string name  = "TransactionManager");
    super.new(name);
    m_usbdev_packetiser = new;
    m_usbdev_packet_classifier = new;
    m_usbdev_data_integrity =new;
    m_token_pkt = new();
    m_data_pkt = new();
    m_handshake_pkt = new();
    state = 2'b0;
    pid = 8'b0;
    address = 7'b0;
    endpoint = 4'b0;
  endfunction

  task transaction_manager( input bit t_pkt[], input bit d_pkt[],
  input bit h_pkt[]);
    m_usbdev_packet_classifier.checkPacket(t_pkt);
    if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_SETUP)  begin
        setup_transaction(d_pkt,h_pkt);
    end
    if (m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_IN) begin
        in_transaction(d_pkt,h_pkt);
    end
    if(m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::TOKEN_OUT) begin
        out_transaction(d_pkt,h_pkt);
    end
  endtask

  task setup_transaction(input bit d_pkt[], input bit h_pkt[]);
    case(state)
       0: begin
         if(m_usbdev_packet_classifier.pid == 8'b1101_0010) begin
           pid = m_usbdev_packet_classifier.pid;
           address = m_usbdev_packet_classifier.address;
           endpoint = m_usbdev_packet_classifier.endpoint;
           m_token_pkt.send_token_packet(pid,address,endpoint);
           state = 1;
         end
       end
       1: begin
         m_usbdev_packet_classifier.checkPacket(d_pkt);
         if(m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_0 ) begin
           pid = m_usbdev_packet_classifier.pid;
           data = m_usbdev_packet_classifier.data;
           m_data_pkt.send_data_packet(pid,data);
           m_usbdev_data_integrity.write(pid,address,endpoint,data);
           state = 2;
         end
       end
       2: begin // wait for handshake Assuming HANDSHAKE packet is sent by the device as an ACK TODO
         `uvm_info(get_type_name(),"ACK Handshake",UVM_LOW);
         state = 0;
       end
       default: state =0;
    endcase
  endtask

  task in_transaction(input bit d_pkt[], input bit h_pkt[]);
    case(state)
      0: begin // address and endpoint sent to data_integrity
        if(m_usbdev_packet_classifier.pid == 8'b1001_0110 ) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid,address,endpoint);
          state = 1;
        end
      end
      1: begin // Getting data from data integrity
        m_usbdev_data_integrity.read(pid,address,endpoint,data);
        m_data_pkt.send_data_packet(pid,data);
        state = 2;
      end
      2: begin
        m_usbdev_packet_classifier.checkPacket(h_pkt);
        if(m_usbdev_packet_classifier.pid == 8'b0010_1101 ) begin
          `uvm_info(get_type_name(),"ACK Handshake",UVM_LOW);
          state = 0;
        end
        else if(m_usbdev_packet_classifier.pid == 8'b1010_0101 ) begin
          `uvm_info(get_type_name(),"NAK Handshake",UVM_LOW);
          state = 0;
        end
        else if(m_usbdev_packet_classifier.pid == 8'b1110_0001 ) begin
          `uvm_info(get_type_name(),"STALL Handshake",UVM_LOW);
          state = 0;
        end
      end
      default: state =0;
    endcase
  endtask

  task out_transaction(input bit d_pkt[], input bit h_pkt[]);
    case(state)
      0: begin //address and endpoint sent to data_integrity
        if(m_usbdev_packet_classifier.pid == 8'b0001_1110 ) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid,address,endpoint);
          state = 1;
        end
      end
      1: begin // Sending data to data integrity
        m_usbdev_packet_classifier.checkPacket(d_pkt);
        if(m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_0 ||
        m_usbdev_packet_classifier.packetType == usbdev_packet_classifier::DATA_1) begin
          pid = m_usbdev_packet_classifier.pid;
          data = m_usbdev_packet_classifier.data;
          m_data_pkt.send_data_packet(pid,data);
          m_usbdev_data_integrity.write(pid,address,endpoint,data);
          state = 2;
        end
      end
      2: begin // TODO Simulate the reception of a HANDSHAKE packet from the device.
        // Currently assuming that the HANDSHAKE packet is an ACKNOWLEDGE
        `uvm_info(get_type_name(),"ACK Handshake",UVM_LOW);
        state = 0;
      end
      default: state =0;
    endcase
  endtask
endclass
