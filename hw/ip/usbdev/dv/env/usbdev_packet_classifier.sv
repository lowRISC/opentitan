// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_packet_classifier extends uvm_object;
  `uvm_object_utils(usbdev_packet_classifier)

  // Packet fields
  logic [7:0]  pid;            // Packet ID identifier
  logic [6:0]  address;        // Address field for token packets
  logic [3:0]  endpoint;       // Endpoint field for token packets
  logic [10:0] frameNumber;    // Frame number for SOF packets
  bit          data[];         // Data fields for data packets
  logic [4:0]  crc5;           // CRC5 field for token packets
  logic [15:0] crc16;          // CRC16 field for data packets
  pid_type_e   m_pid_type;     // Type of pid

  // Constructor
  function new(string name = "packet_classifier");
    super.new(name);
    pid         = '0;
    address     = '0;
    endpoint    = '0;
    frameNumber = '0;
    crc5        = '0;
    crc16       = '0;
  endfunction

  // Function to check the packet
  function void checkPacket(input bit  pkt[]);
    for (int i = 0; i <= 7; i++) begin
      pid = {pid, pkt[i]};
    end

    m_pid_type = pid_type_e'(pid);
    case (m_pid_type)
      PidTypeSetupToken, PidTypeInToken, PidTypeOutToken: begin
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
      PidTypeSofToken: begin
        for(int i = 8; i <= 18; i++) begin
          frameNumber  = {frameNumber, pkt[i]};
        end
        for(int i = 19; i <= 23; i++) begin
          crc5 = {crc5, pkt[i]};
        end
      end
      PidTypeData0, PidTypeData1: begin
        data.delete();
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
  endfunction

endclass
