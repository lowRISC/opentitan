// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_seq_item extends uvm_sequence_item;

  // Knobs //
  // min number of data bytes
  int    data_len_max;
  // Max number of data bytes
  int    data_len_min;


  // randomized values //
  rand bit                                 mode; // TODO implement this as enum
  // 0: auto start, 1: wait for start
  rand bit                                 man_trigger;
  // 0: output data cannot be overwritten
  // 1: new output will overwrite old output even if not read.
  rand bit                                 allow_data_ovrwrt;
  // lenth of plaintext / cypher
  rand bit                   [31:0]        data_len;
  // key len 0: 128, 1: 192, 2: 256 3: NOT VALID
  rand bit                   [2:0]         key_size;
  // 256 bit key (8x32 bit)
  rand bit              [7:0][31:0]        key;
  // data queue to hold the randomized data
  rand bit                   [31:0]        data_in_queue[$];
  // randomized data to add to queue




  // fixed variables //
  // indicated which words has data
  bit [3:0] data_in_vld  = 4'b0;
  // indicated which words has data
  bit                         [3:0]       data_out_vld = 4'b0;
  // used by the checker
  bit                   [3:0][31:0]       data_in;
  // used by the checker
  bit                   [3:0][31:0]       data_out;
  // used to store output data
  bit                        [31:0]       data_out_queue[$];
  // set if data should be fixed and not randomized
  bit                                     fixed_data = 0;
  // if set unused key bytes will be forced to 0 - controlled from test
  bit                                     key_mask=0;



  function new( string name="aes_sequence_item");
    super.new(name);
  endfunction


  // contraints //
  constraint c_data {
    solve data_len before data_in_queue;
    data_len inside { [data_len_min: data_len_max] };

    if(data_len[1:0] == 2'b00) {
      data_in_queue.size() == data_len >> 2;
    } else {
      data_in_queue.size() ==  data_len >> 2 + 1;
    }
    if(data_len[1:0] == 2'b01) {
      data_in_queue[$][31:8]   == 0;
    } else if (data_len[1:0] == 2'b10) {
      data_in_queue[$][31:16]  == 0;
    } else {
      data_in_queue[$][31:24]  == 0;
    }
  }

  constraint c_key_size {key_size inside {3'b001, 3'b010, 3'b100 };
             // key len 0: 128, 1: 192, 2: 256 3: NOT VALID
  }

  constraint c_mode_reg {mode == 0; man_trigger == 0; allow_data_ovrwrt == 0; }

  function void post_randomize();
    if(key_mask) begin
      case (key_size)
        3'b001: begin
          key[7:4] = 32'h00000000;
        end
        3'b010: begin
          key[7:6] = 32'h00000000;
        end
        default: begin
        end
      endcase
    end
  endfunction


  function bit add2output( logic [31:0] data );
    data_out_queue.push_back(data);
    return 1;
  endfunction


  virtual function void do_copy(uvm_object rhs);
    aes_seq_item rhs_;

    if(!$cast(rhs_,rhs) ) begin
      uvm_report_error("do_copy:", "acst failed");
      return;
    end
    super.do_copy(rhs);
    mode     = rhs_.mode;
    data_in  = rhs_.data_in;
    key      = rhs_.key;
    key_size = rhs_.key_size;
    data_out = rhs_.data_out;
  endfunction // copy


// do compare //
virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);

  aes_seq_item rhs_;

  if(!$cast(rhs_,rhs))begin
    return 0; // compare failed because object is not of sequence item type
  end

return(super.do_compare(rhs,comparer) &&
  (mode     == rhs_.mode) &&
  (data_in  == rhs_.data_in) &&
  (key      == rhs_.key) &&
  (data_out == rhs_.data_out) );
endfunction // compare


// convert to string //
virtual function string convert2string();
 string str;
  str = super.convert2string();
  str = {str,  $psprintf("\n\t ----| AES SEQUENCE ITEM                                  |----\t ")
        };
  str = {str,  $psprintf("\n\t ----| Mode:    \t %s                          |----\t ",
        (mode==1'b0) ? "ENCRYPT" : "DECRYPT" ) };
  str = {str,  $psprintf("\n\t ----| Key size:    \t %s                             |----\t ",
         (key_size==3'b001) ? "128b" : (key_size == 3'b010) ? "192b" : "256b") };
  str = {str,  $psprintf("\n\t ----| Key:         \t ") };
  for(int i=0; i <8; i++) begin
    str = {str, $psprintf("%h ",key[i])};
  end
  str = {str,  $psprintf("\n\t ----| Input data:  \t %h |----\t ", data_in) };
  str = {str,  $psprintf("\n\t ----| Output data: \t %h |----\t ", data_out) };
  str = {str,  $psprintf("\n\t") };

  return str;
  endfunction // conver2string

  virtual function string bytes2string();
    string str="\n\t ----| data_out: ";
    for(int i=0; i<4; i++) begin
        str = {str, $psprintf("%h", data_out[i][31:0])};
    end
    return str;
  endfunction

`uvm_object_utils(aes_seq_item)

endclass
