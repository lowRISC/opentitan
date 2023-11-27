// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_manager class
// -------------------------------
class usbdev_pkt_manager extends uvm_object;
  `uvm_object_utils(usbdev_pkt_manager)

  //This queue is used to store the expected packet.
  static bit exp_q[$][];

  function new(string name = "usbdev_pkt_manager");
    super.new(name);
  endfunction

  // pop_packet task to pop the expected packet
  // -------------------------------
  task pop_packet(output bit expected_pkt[]);
    if (exp_q.size() > 0) begin
       expected_pkt = exp_q.pop_back();
    end
    else
      `uvm_info(get_type_name(),"QUEUE IS EMPTY",UVM_LOW);
  endtask

   // push_packet task to push the expected packet
  // -------------------------------
  task push_packet(bit exp_pkt []);
    exp_q.push_front(exp_pkt);
  endtask
endclass

// Token_packet class
// -------------------------------
class token_packet extends usbdev_pkt_manager;
  logic [7:0]  sync;
  logic [7:0]  pid;
  logic [6:0]  addr;
  logic [3:0]  endp;
  logic [4:0]  crc5;
  logic [2:0]  eop;
  bit pack_token[];

  `uvm_object_utils_begin (token_packet)
    `uvm_field_int(sync, UVM_ALL_ON)
    `uvm_field_int(pid, UVM_ALL_ON)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(endp, UVM_ALL_ON)
    `uvm_field_int(crc5, UVM_ALL_ON)
    `uvm_field_int(eop, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "token_packet");
    super.new(name);
    this.sync = 0;
    this.pid  = 0;
    this.addr = 0;
    this.endp = 0;
    this.crc5 = 0;
    this.eop  = 0;
  endfunction

  // send_token_packet task : To get the fields of token packet and pack them and then send that
  // packet into expected queue
  // -------------------------------
  task send_token_packet(bit[7:0] tpid,bit[6:0] taddress,bit[3:0] tendpoint);
    bit [4:0] crc;
    bit [10:0] data;
    bit [4:0] polynomial = 5'b0_0101;
    data = {tendpoint,taddress};

    // Calculate crc5
    crc = 5'b1_1111;
    for (int i = 0; i <= 10; i++) begin
      if ((crc[4] ^ data[i]) == 1) begin
        crc = {crc[3:0], 1'b0} ^ polynomial;
      end
      else begin
        crc = {crc[3:0], 1'b0};
      end
    end
    crc = ~crc;

    // Bit streaming to send LSB first...
    this.sync = 8'b0000_0001;
    this.pid  = {<<4{tpid}};
    this.pid  = {<<{this.pid}};
    taddress  = {<<{taddress}};
    this.addr = taddress;
    tendpoint = {<<{tendpoint}};
    this.endp = tendpoint;
    this.crc5 = crc;
    this.eop  = 3'b001;
    // Pack the token packet
    this.pack(pack_token);
    super.push_packet(pack_token);
  endtask
endclass

// data_packet class
// -------------------------------
class data_packet extends usbdev_pkt_manager;
  logic [7:0]   sync;
  logic [7:0]   pid;
  logic data    [];
  logic [15:0]  crc16;
  logic [2:0]   eop;
  bit pack_data [];

  `uvm_object_utils_begin (data_packet)
    `uvm_field_int(sync, UVM_ALL_ON)
    `uvm_field_int(pid, UVM_ALL_ON)
    `uvm_field_array_int(data, UVM_ALL_ON)
    `uvm_field_int(crc16, UVM_ALL_ON)
    `uvm_field_int(eop, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "data_packet");
    super.new(name);
    this.sync = 0;
    this.pid  = 0;
    foreach(data[i])
      this.data[i] = 0;
    this.crc16 = 0;
    this.eop = 0;
  endfunction

  // send_data_packet task : To get the fields of data packet and pack them and then send that
  // packet into expected queue
  // -------------------------------
  task send_data_packet(bit[7:0] dpid,bit ddata []);
    bit [15:0] crc;
    bit [15:0] polynomial = 16'h8005;

    // store the data bit by bit in dynamic array
    foreach(ddata[i]) begin
      this.data = new[this.data.size() + 1](this.data);
      this.data[this.data.size() - 1] = ddata[i];
    end
    crc = 16'b1111_1111_1111_1111;

    // Shift and re_order each byte to send LSB first
    data  = {<<8{data}};
    data  = {<<{data}};

    // Calculate crc16
    for (int i = 0; i < data.size(); i++) begin
      if ((crc[15] ^ data[i]) == 1) begin
        crc = {crc[14:0], 1'b0} ^ polynomial;
      end
      else begin
        crc = {crc[14:0], 1'b0};
      end
    end
    crc = ~crc;

    this.sync  = 8'b0000_0001;
    this.pid   = {<<4{dpid}};
    this.pid  = {<<{this.pid}};
    this.crc16 = crc;
    this.eop   = 3'b001;
    // Pack the data packet
    this.pack(pack_data);
    super.push_packet(pack_data);
    data.delete();
  endtask
endclass

// hand_shake_packet class
// -------------------------------
class hand_shake_packet extends usbdev_pkt_manager;
  logic [7:0] sync;
  logic [7:0] pid;
  logic [2:0] eop;
  bit pack_handshake[];

  `uvm_object_utils_begin (hand_shake_packet)
    `uvm_field_int(sync,UVM_ALL_ON)
    `uvm_field_int(pid,UVM_ALL_ON)
    `uvm_field_int(eop,UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "hand_shake_packet");
    super.new(name);
    this.sync = 0;
    this.pid  = 0;
    this.eop  = 0;
  endfunction

  // send_handshake_packet task : To get the field of data packet and pack them and then send that
  // packet into expected queue
  task send_handshake_packet(bit[7:0] hpid);
    this.sync  = 8'b0000_0001;
    this.pid   = {<<4{hpid}};
    this.pid  = {<<{this.pid}};
    this.eop   = 3'b001;
    // Pack the handshake packet
    this.pack(pack_handshake);
    super.push_packet(pack_handshake);
  endtask
endclass
