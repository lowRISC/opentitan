// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_item extends uvm_sequence_item;
  pid_type_e m_pid_type;
  pkt_type_e m_pkt_type;
  bmrequesttype_e m_bmRT;
  brequest_e m_bR;

  `uvm_object_new

endclass

class token_pkt extends usb20_item;
  rand bit [6:0] address;
  rand bit [3:0] endpoint;
  bit [4:0] crc5;

  constraint endpoint_c {
    endpoint inside {[0:11]};
  }

  `uvm_object_utils_begin(token_pkt)
    `uvm_field_enum(pid_type_e, m_pid_type, UVM_DEFAULT)
    `uvm_field_int(address,                 UVM_DEFAULT)
    `uvm_field_int(endpoint,                UVM_DEFAULT)
    `uvm_field_int(crc5,                    UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void post_randomize();
    crc5 = generate_crc5(address, endpoint);
  endfunction
  function bit [4:0] generate_crc5(bit [6:0] address, bit [3:0] endpoint);
    bit [4:0] crc;
    bit [4:0] crc_reg;
    bit [10:0] data;
    bit [4:0] polynomial = 5'b0_0101;
    bit       as1;
    bit [4:0] as2;
    data = {endpoint, address};
    crc_reg = 5'b1_1111;
    for (int i = 0; i <= 10; i++) begin
      as1 = data[i] ^ crc_reg[4];
      as2 = ({crc_reg[3:2], (as1 ^ crc_reg[1]), crc_reg[0], as1});
      crc_reg = as2;
    end
    crc = ~{crc_reg[0], crc_reg[1], crc_reg[2], crc_reg[3], crc_reg[4]};
    return crc;
  endfunction
endclass

class data_pkt extends usb20_item;
  bit [15:0] crc16;
  rand byte unsigned  data[]; // Dynamic array

  `uvm_object_utils_begin(data_pkt)
    `uvm_field_enum(pid_type_e, m_pid_type, UVM_DEFAULT)
    `uvm_field_array_int(data,              UVM_DEFAULT)
    `uvm_field_int(crc16,                   UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  constraint data_c {
    data.size() <= 64;
   }

  function void set_payload(byte bmRequestType, byte bRequest, byte wVH, byte wVL, byte wIH,
                            byte wIL, byte wLH, byte wLL);

    data = '{bmRequestType, bRequest, wVH, wVL, wIH, wIL, wLH, wLL};
    crc16 = generate_crc16(data);
  endfunction

  function void post_randomize();
    crc16 = generate_crc16(data);
  endfunction

  function bit [15:0] generate_crc16(input byte unsigned data[]);
    bit [15:0] crc;
    bit [15:0] crc_reg;
    bit        as1;
    bit [15:0] as2;
    bit [15:0] polynomial = 16'h8005;
    bit data1[];
    typedef bit data_result[] ;
    data_result data_array;
    data_array = data_result'(data);
    crc = 16'b1111_1111_1111_1111;
    data_array = {<<8{data_array}};
    data_array = {<<{data_array}};
    for (int i = 0; i < data_array.size(); i++) begin
      if ((crc[15] ^ data_array[i]) == 1) begin
        crc = {crc[14:0], 1'b0} ^ polynomial;
      end
      else begin
        crc = {crc[14:0], 1'b0};
      end
    end
    crc = ~crc;
    crc = {<<{crc}};
    return crc;
  endfunction
endclass

class sof_pkt extends usb20_item;
  rand bit [10:0] framecnt ;
  bit [4:0] crc5;

  `uvm_object_utils_begin (sof_pkt)
    `uvm_field_enum(pid_type_e, m_pid_type, UVM_DEFAULT)
    `uvm_field_int(framecnt,                UVM_DEFAULT)
    `uvm_field_int(crc5 ,                   UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void post_randomize();
    crc5 = generate_crc5();
  endfunction

  function bit [4:0] generate_crc5();
    bit [4:0] crc;
    bit [4:0] crc_reg;
    bit [10:0] data;
    bit [4:0] polynomial = 5'b0_0101;
    bit       as1;
    bit [4:0] as2;
    data = framecnt;
    crc_reg = 5'b1_1111;
    for (int i = 0; i <= 10; i++) begin
      as1 = data[i] ^ crc_reg[4];
      as2 = ({crc_reg[3:2], (as1 ^ crc_reg[1]), crc_reg[0], as1});
      crc_reg = as2;
    end
    crc = ~{crc_reg[0], crc_reg[1], crc_reg[2], crc_reg[3], crc_reg[4]};
    return crc;
  endfunction

endclass

class handshake_pkt extends usb20_item;

  `uvm_object_utils_begin (handshake_pkt)
    `uvm_field_enum(pid_type_e, m_pid_type, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
