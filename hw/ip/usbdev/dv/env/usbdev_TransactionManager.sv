// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_TransactionManager extends uvm_object;
  `uvm_object_utils(usbdev_TransactionManager)

  // Enumeration for the type of transfer
  typedef enum bit [1:0] {
  CONTROL_TRANSFER = 2'b00,
  INTERRUPT_TRANSFER = 2'b01,
  ISOCHRONOUS_TRANSFER = 2'b10,
  BULK_TRANSFER = 2'b11
  } transfertype_e;

  typedef enum bit[1:0] {
  idle_stage =2'b00,
  setup_stage = 2'b10,
  data_stage =2'b01,
  status_stage = 2'b11
  }control_transfer_stages_e;

  usbdev_packetiser m_usbdev_packetiser;
  usbdev_packet_classifier m_usbdev_packet_classifier;
  usbdev_data_integrity  m_usbdev_data_integrity;
  token_packet      m_token_pkt;
  data_packet       m_data_pkt;
  hand_shake_packet m_handshake_pkt;
  transfertype_e mTransferType;
  logic [1:0]state;
  logic [15:0]crc16;
  logic [6:0] address;
  logic [3:0] endpoint;
  bit data[];
  bit [7:0] pid;
  bit  payload_out [];
  bit t_pkt[];
  bit d_pkt[];
  bit h_pkt[];
  control_transfer_stages_e stage;

  function new(string name  = "TransactionManager");
    super.new(name);
    m_usbdev_packetiser = new;
    m_usbdev_packet_classifier = new;
    m_usbdev_data_integrity =new;
    m_token_pkt = new();
    m_data_pkt = new();
    m_handshake_pkt = new();
    stage = setup_stage;
    state = 2'b0;
    pid = 8'b0;
    address = 7'b0;
    endpoint = 4'b0;
    t_pkt =m_usbdev_packetiser.token_pkt_arr;
    d_pkt =m_usbdev_packetiser.data_pkt_arr;
    h_pkt =m_usbdev_packetiser.handshake_pkt_arr;
  endfunction

  task transaction_manager(input bit [1:0] mTransferType , input bit t_pkt[], input bit d_pkt[],
  input bit h_pkt[]);
    m_usbdev_packet_classifier.checkPacket(t_pkt);
    case (mTransferType)
      CONTROL_TRANSFER: begin
        if (m_usbdev_packet_classifier.packetType == 4'b1101)  begin
          for(int i=0 ;i<=2;i++) begin
            control_interupt_stages(t_pkt, d_pkt, h_pkt);
          end
        end
      end
      INTERRUPT_TRANSFER: begin
        if (m_usbdev_packet_classifier.packetType == 4'b1001) begin
          for(int i=0 ;i<=2;i++) begin
            in_transaction(d_pkt,h_pkt);
          end
        end
        else if(m_usbdev_packet_classifier.packetType == 4'b0001) begin
          for(int i=0 ;i<=2;i++) begin
            out_transaction(d_pkt,h_pkt);
          end
        end
      end
      ISOCHRONOUS_TRANSFER: begin
        if(m_usbdev_packet_classifier.packetType == 4'b1001) begin
          for(int i=0 ;i<=1;i++) begin
            in_data();
          end
        end
        else if(m_usbdev_packet_classifier.packetType == 4'b0001) begin
          for(int i=0 ;i<=1;i++) begin
            out_data(d_pkt);
          end
        end
      end
      BULK_TRANSFER: begin
        if (m_usbdev_packet_classifier.packetType == 4'b1001) begin
          for(int i=0 ;i<=2;i++) begin
            in_transaction(d_pkt,h_pkt);
          end
        end
        else if(m_usbdev_packet_classifier.packetType == 4'b0001) begin
          for(int i=0 ;i<=2;i++) begin
            out_transaction(d_pkt,h_pkt);
          end
        end
      end
      default: begin
      end
    endcase
  endtask

  task control_interupt_stages( input bit t_pkt[], input bit d_pkt[], input bit h_pkt[]);
    case(stage)
      setup_stage: begin
        if (m_usbdev_packet_classifier.pid== 8'b1101_0010) begin
          for(int i=0 ;i<=2;i++) begin
            setup_transaction(d_pkt);
          end
          stage = data_stage;
        end
      end
      data_stage: begin
        m_usbdev_packet_classifier.checkPacket(t_pkt);
        if (m_usbdev_packet_classifier.packetType == 4'b1001) begin
          for(int i=0 ;i<=2;i++) begin
            in_transaction(d_pkt,h_pkt);
          end
          stage = status_stage;
        end
        else if(m_usbdev_packet_classifier.packetType == 4'b0001) begin
          for(int i=0 ;i<=2;i++) begin
            out_transaction(d_pkt,h_pkt);
          end
          stage = status_stage;
        end
      end
      status_stage: begin
        $display("status stage");
        stage = setup_stage;
      end
      default: stage = idle_stage;
    endcase
  endtask

  task setup_transaction(input bit d_pkt[]);
    case(state)
       0: begin //address and endpoint sent to data_integrity
         if(m_usbdev_packet_classifier.pid == 8'b1101_0010) begin
           address = m_usbdev_packet_classifier.address;
           endpoint = m_usbdev_packet_classifier.endpoint;
           state = 1;
         end
       end
       1: begin //Getting data from data integrity
         m_usbdev_packet_classifier.checkPacket(d_pkt);
         if(m_usbdev_packet_classifier.packetType == 4'b0011 ) begin
           pid = m_usbdev_packet_classifier.pid;
           data = m_usbdev_packet_classifier.data;
           m_usbdev_data_integrity.write(pid,address,endpoint,data);
           state = 2;
         end
       end
       2: begin //wait for handshake Assuming HANDSHAKE packet is sent by the device as an ACK TODO
         $display("ACK handshake");
         state = 0;
       end
       default: state =0;
    endcase
  endtask

  task in_transaction(input bit d_pkt[], input bit h_pkt[]);
    case(state)
      0: begin //address and endpoint sent to data_integrity
        if(m_usbdev_packet_classifier.pid == 8'b1001_0110 ) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid,address,endpoint);
          state = 1;
        end
      end
      1: begin //Getting data from data integrity
        m_usbdev_data_integrity.read(pid,address,endpoint,data);
        m_data_pkt.send_data_packet(pid,data);
        state = 2;
      end
      2: begin//wait for handshake //Assuming HANDSHAKE packet is sent by the device as an ACK
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
      0: begin//add and endpoint sent to data_integrity
        if(m_usbdev_packet_classifier.pid == 8'b0001_1110 ) begin
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          pid = m_usbdev_packet_classifier.pid;
          state = 1;
        end
      end
      1: begin //Sending data to data integrity
        m_usbdev_packet_classifier.checkPacket(d_pkt);
        if(m_usbdev_packet_classifier.packetType == 4'b0011 ||
        m_usbdev_packet_classifier.packetType == 4'b1011) begin
          pid = m_usbdev_packet_classifier.pid;
          data = m_usbdev_packet_classifier.data;
          m_usbdev_data_integrity.write(pid,address,endpoint,data);
          state = 2;
        end
      end
      2: begin// TODO Simulate the reception of a HANDSHAKE packet from the device.
        //Currently assuming that the HANDSHAKE packet is an ACKNOWLEDGE
        $display("Ack handshake");
        state = 0;
      end
      default: state =0;
    endcase
  endtask

  task in_data(); //IN_token -> Data
    case(state)
      0: begin
        if(m_usbdev_packet_classifier.pid == 8'b1001_0110 ) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          m_token_pkt.send_token_packet(pid,address,endpoint);
          state = 1;
        end
      end
      1: begin
        m_usbdev_data_integrity.read(pid,address,endpoint,data);
        m_data_pkt.send_data_packet(pid,data);
        state = 0;
      end
      default: state =0;
    endcase
  endtask

  task out_data(input bit d_pkt[]);
    case(state)
      0: begin
        if(m_usbdev_packet_classifier.pid == 8'b0001_1110 ) begin
          pid = m_usbdev_packet_classifier.pid;
          address = m_usbdev_packet_classifier.address;
          endpoint = m_usbdev_packet_classifier.endpoint;
          state = 1;
        end
      end
      1: begin
        m_usbdev_packet_classifier.checkPacket(d_pkt);
        if(m_usbdev_packet_classifier.packetType == 4'b0011 ||
        m_usbdev_packet_classifier.packetType == 4'b1011) begin
          data = m_usbdev_packet_classifier.data;
          m_usbdev_data_integrity.write(pid,address,endpoint,data);
          state = 0;
        end;
       end
       default: state =0;
    endcase
  endtask
endclass
