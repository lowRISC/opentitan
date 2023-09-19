// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0



typedef enum bit [2:0] {token, data, handshake, SOF} pkt_type;

virtual class usb20_item extends uvm_sequence_item;
    rand bit [7:0]	pid;
    pkt_type type1;
	    //`uvm_object_utils_begin (usb20_item)
			//`uvm_field_int(pid, UVM_ALL_ON)
			//`uvm_field_enum(pkt_type, type1, UVM_ALL_ON)
      //`uvm_object_utils_end
      function new(string name = "usb20_item");
        super.new(name);
      endfunction

endclass

/////////////////////////handshake packet//////////////////////////

class handshake_pkt extends usb20_item;

    `uvm_object_utils_begin (handshake_pkt)
			`uvm_field_int(pid, UVM_ALL_ON)
    `uvm_object_utils_end

     function new(string name = "handshake_pkt");
        super.new(name);
      endfunction
      /*constraint type1{
          data.size() inside {[0:1023]};
      }*/
endclass

///////////////////////////data packet////////////////////////////

class data_pkt extends usb20_item;

			rand bit [15:0] crc16;
			rand bit [7:0] data [];
			//bit [7:0] sync_pattern = 8'b01010100;
      //bit [1:0] eop;

    `uvm_object_utils_begin (data_pkt)
      //`uvm_field_int(sync_pattern, UVM_ALL_ON)
			`uvm_field_int(crc16, UVM_ALL_ON)
			`uvm_field_array_int(data, UVM_ALL_ON)
			 `uvm_field_int(pid, UVM_ALL_ON)
			//`uvm_field_int(eop, UVM_ALL_ON)
    `uvm_object_utils_end

      constraint address_limit{
          data.size() inside {[0:1023]};
      }
      /*function bit [4:0] generate_crc5();
        bit [5:0] crc = 6'b000000;
        bit [15:0] data;
        bit [5:0] polynomial = 6'b100101;
        data = {address, endpoint, 5'b00000};
        $display("data %b" , data);
        crc = data[15:10] ^ polynomial;
        $display("crc_initial %b" , crc);
        for(int j = 9; j>=0; j--) begin 
         if((crc[4] == 0) & (crc[5] == 0))
         begin
          crc = {crc , data[j], data[j-1]};
          $display("crc_added2 %b",crc);
          crc = crc ^ polynomial;
          $display("i= %d crc_0 %b",j,crc);
          j = j-1;
         end
         else if((crc[4] == 1) & (crc[5] == 0))
         begin
          crc = {crc , data[j]};
          $display("crc_added1 %b",crc);
          crc = crc ^ polynomial;
          $display("i= %d crc_1 %b" ,j,crc);
         end
         else
         begin
          crc = crc ^ polynomial;
          $display("i= %d crc_2 %b" ,j,crc);
          end
        end
        return crc;
    endfunction*/
    function new(string name = "data_pkt");
        super.new(name);
    endfunction

endclass

///////////////////////////token packet//////////////////////////

class token_pkt extends usb20_item;

      rand bit [6:0] address;
      rand bit [3:0] endpoint;
      bit [4:0] crc5;

      `uvm_object_utils_begin (token_pkt)
      //`uvm_field_int(sync_pattern, UVM_ALL_ON)
      `uvm_field_int(crc5, UVM_ALL_ON)
      `uvm_field_int(endpoint, UVM_ALL_ON)
      `uvm_field_int(address, UVM_ALL_ON)
      `uvm_field_int(pid, UVM_ALL_ON)

    `uvm_object_utils_end

    function void post_randomize();
        crc5 = generate_crc5();
    endfunction

    function bit [4:0] generate_crc5();
        bit [5:0] crc = 6'b000000;
        bit [15:0] data;
        bit [5:0] polynomial = 6'b100101;
        data = {address, endpoint, 5'b00000};
        crc = data[15:10] ^ polynomial;
        for(int j = 9; j>=0; j--) begin
         if((crc[4] == 0) & (crc[5] == 0))
         begin
          crc = {crc , data[j], data[j-1]};
          $display("crc_added2 %b",crc);
          crc = crc ^ polynomial;
          j = j-1;
         end
         else if((crc[4] == 1) & (crc[5] == 0))
         begin
          crc = {crc , data[j]};
          $display("crc_added1 %b",crc);
          crc = crc ^ polynomial;
         end
         else
         begin
          crc = crc ^ polynomial;
          end
        end
        return crc;
    endfunction
    function new(string name = "token_pkt");
        super.new();
    endfunction

endclass
