// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_packet_classifier extends uvm_object;
  `uvm_object_utils(usbdev_packet_classifier)

  // Define packet types
  typedef enum logic [3:0] {
  TOKEN_SETUP = 4'b0010,
  TOKEN_IN = 4'b0110,
  TOKEN_OUT = 4'b1110,
  SOF = 4'b1010,
  DATA_0 = 4'b1100,
  DATA_1 = 4'b0100,
  HANDSHAKE_ACK = 4'b1101,
  HANDSHAKE_NACK = 4'b0101,
  HANDSHAKE_STALL = 4'b0001,
  UNSUPPORTED_PACKET = 4'b0000
  }usbpackettype_e;
  // Packet fields
  bit [3:0] pid_iden;         // Packet ID identifier
  logic [7:0] pid;            // Packet ID identifier
  logic [6:0] address;        // Address field for token packets
  logic [3:0] endpoint;       // Endpoint field for token packets
  logic [10:0] frameNumber;   // Frame number for SOF packets
  bit data[];                 // Data fields for data packets
  logic [4:0] crc5;           // CRC5 field for token packets
  logic [15:0] crc16;         // CRC16 field for data packets
  usbpackettype_e packetType; // Type of packet

  // Constructor
  function new(string name  = "packet_classifier");
    super.new(name);
    pid_iden = 4'b0000;
    pid = 8'b00000000;
    address = 7'b0000000;
    endpoint = 4'b0000;
    frameNumber = 11'b00000000000;
    crc5 = 5'b00000;
    crc16 = 16'b0000000000000000;
    packetType = UNSUPPORTED_PACKET;
  endfunction
  // Function to check the packet
  function void checkPacket(input bit  pkt[]);
    for(int i = 0; i <= 3; i++) begin
      pid_iden = {pid_iden, pkt[i]};
    end
    packetType = usbpackettype_e'(pid_iden);
    for (int i = 0; i <= 7; i++) begin
      pid = {pid, pkt[i]};
    end
    if(packetType == UNSUPPORTED_PACKET)
      return;
    else begin
      case (packetType)
        TOKEN_SETUP,TOKEN_IN,TOKEN_OUT: begin
          for (int i = 8; i <= 14; i++) begin
            address = {address, pkt[i]};
          end
          for (int i = 15; i <= 18; i++) begin
            endpoint = {endpoint, pkt[i]};
          end
          for (int i = 19; i <= 23; i++) begin
            crc5 = {crc5, pkt[i]};
          end
        end
        SOF: begin
          for(int i = 8; i <= 18; i++) begin
            frameNumber  = {frameNumber , pkt[i]};
          end
          for(int i = 20; i <= 23; i++) begin
            crc5 = {crc5, pkt[i]};
          end
        end
        DATA_0, DATA_1: begin
          for(int i = 8; i < pkt.size()-16; i++) begin
            data = new[data.size() +1](data);
            data[data.size() - 1] = pkt[i];
          end
          for(int i = pkt.size() - 16; i <= pkt.size() - 1; i++) begin
            crc16 = {crc16, pkt[i]};
          end
        end
        default: begin
        end
      endcase
    end
  endfunction
// Function to validate the packet (CRC check)
  function bit crc_error();
    if ((packetType == TOKEN_SETUP) || (packetType == TOKEN_IN) || (packetType == TOKEN_OUT))begin
      bit [4:0] crc5_polynomial = 5'b00101;
      for(int i = 0; i < 5; i = i + 1)begin
        if (crc5[4]==1)begin
          crc5 = {crc5[3:0], 1'b0} ^ crc5_polynomial;
        end
        else
          crc5 = {crc5[3:0], 1'b0};
      end
      if (crc5 == 5'b00000)
        return 0;
      else
        return 1;
      end
    else if ((packetType == DATA_0) ||(packetType == DATA_1))begin
      bit [15:0] crc16_polynomial = 16'h8005;
      for (int i = 0; i < 16; i = i + 1)begin
        if (crc16[15]==1) begin
          crc16 = {crc16[14:0], 1'b0} ^ crc16_polynomial;
        end
        else
          crc16 = {crc16[14:0], 1'b0};
      end
      if (crc16 == 16'b0000000000000000)
        return 0;
      else
        return 1;
      end
  endfunction
endclass
