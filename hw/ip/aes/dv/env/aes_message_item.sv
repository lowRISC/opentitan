// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_message_item extends uvm_sequence_item;

  `uvm_object_utils(aes_message_item)

  `uvm_object_new

  ///////////////////////////////////////
  //  control Knobs                    //
  ///////////////////////////////////////

  // min number of data bytes
  int    message_len_max     = 16;
  // Max number of data bytes
  int    message_len_min     = 1;
  // percentage of configuration errors
  int    config_error_pct    = 20;
  // errors enabled
  bit    errors_en           = 1;
  // configuraiton errors enabled
  bit    config_err          = 0;

  // Mode distribution //
  // chance of selection ecb_mode
  // ecb_mode /(ecb_mode + cbc_mode + ctr_mode)
  // with the defaults 10/30 = 1/3 (33%)
  int    ecb_weight          = 10;
  int    cbc_weight          = 10;
  int    ctr_weight          = 10;
  // KEYLEN weights
  int    key_128b_weight     = 10;
  int    key_192b_weight     = 10;
  int    key_256b_weight     = 10;

  ///////////////////////////////////////
  // Randomizable variables            //
  ///////////////////////////////////////

  // length of the message                                     //
  rand int             message_length;
  // mode - which type of ecnryption is used                   //
  rand aes_mode_e      aes_mode;
  // operation - encruption or decryption                      //
  rand aes_op_e        aes_operation;
  // aes key length                                            //
  rand bit [2:0]       aes_keylen;
  // 256 bit key (8x32 bit)                                    //
  rand bit [7:0][31:0] aes_key;
  // 256 bit initialization vector (8x32 bit)                  //
  rand bit [3:0][31:0] aes_iv;
  // configuration error                                       //
  rand bit             has_config_error;

  ///////////////////////////////////////
  // FIXED variables                   //
  ///////////////////////////////////////

  bit [7:0]            input_msg[];
  bit [7:0]            output_msg[];
  bit [7:0]            predicted_msg[];

  ///////////////////////////////////////
  // Constraints                       //
  ///////////////////////////////////////

  constraint c_data { message_length inside { [message_len_min:message_len_max] };}

  constraint c_keylen {
    solve has_config_error before aes_keylen;
    if(!has_config_error) {
      // key len 001: 128, 010: 192, 100: 256
      aes_keylen inside { 3'b001, 3'b010, 3'b100 };
      // mode distribution
      aes_keylen dist  { 3'b001 := key_128b_weight, 3'b010 := key_192b_weight, 3'b100 := key_256b_weight };
    } else {
      !(aes_keylen inside { 3'b001, 3'b010, 3'b100 });  // force the selection to be something invalid     
    }
  }

  constraint c_mode { aes_mode dist  { AES_ECB := ecb_weight, AES_CBC:= cbc_weight, AES_CTR := ctr_weight };}

  constraint c_has_config_error {
    if(errors_en && config_err)
      {
      has_config_error dist { 0 :/ (100-config_error_pct),
                              1 :/ config_error_pct    };
    }
    else { has_config_error == 0; }
  }



  function void add_data_item(aes_seq_item item);
    for(int i=0; i < 4 ; i++ ) begin
      // data_in.push_front (data_in[3:0])
      input_msg  = { input_msg , item.data_in[i][7:0], item.data_in[i][15:8], item.data_in[i][23:16]
                    ,item.data_in[i][31:24]};
      // data_in.push_front (data_in[3:0])
      output_msg = { output_msg, item.data_out[i][7:0], item.data_out[i][15:8],
                     item.data_out[i][23:16],item.data_out[i][31:24] };
    end
  endfunction // add_data_item


  function void add_start_msg_item(aes_seq_item item);
    this.aes_mode      = item.mode;
    this.aes_operation = item.operation;
    this.aes_keylen    = item.key_len;
    this.aes_key       = item.key;

    add_data_item(item);
  endfunction // add_start_msg_item


  function void alloc_predicted_msg();
    predicted_msg = new[input_msg.size()];
  endfunction // alloc_predicted_msg


  // convert to string //
  virtual function string convert2string();
    string str;
    str = super.convert2string();
    str = {str,  $sformatf("\n\t ----| AES MESSAGE ITEM                                  |----\t ")
           };
    str = {str,  $sformatf("\n\t ----| Mode:    \t %s                         |----\t ",
                           aes_mode.name() ) };
    str = {str,  $sformatf("\n\t ----| Operation:    \t %s                     |----\t ",
                           aes_operation.name() ) };
    str = {str,  $sformatf("\n\t ----| has Configuration error:    \t %s           |----\t ",
                           (has_config_error==1) ? "TRUE" : "FALSE" ) };
    str = {str,  $sformatf("\n\t ----| Message Length:    \t %d             |----\t ",
                           message_length ) };

    str = {str,  $sformatf("\n\t ----| Key Length:    \t %03b                             |----\t ",
                           aes_keylen) };
    str = {str,  $sformatf("\n\t ----| Key:         \t ") };
    for(int i=0; i <8; i++) begin
      str = {str, $sformatf("%h ",aes_key[i])};
    end
    str = {str,  $sformatf("\n\t ----| errors_enabled: %b         \t ", errors_en) };
    str = {str,  $sformatf("\n\t ----| config_err: %b         \t ", config_err) };
    str = {str,  $sformatf("\n\t ----| MODE Distribution:     \t " ) };
    str = {str,  $sformatf("\n\t ----| ECB Weight: %d         \t ", ecb_weight) };
    str = {str,  $sformatf("\n\t ----| CBC Weight: %d         \t ", cbc_weight) };
    str = {str,  $sformatf("\n\t ----| CTR Weight: %d         \t ", ctr_weight) };
    str = {str,  $sformatf("\n\t ----| Key Len Distribution   :\t " ) };
    str = {str,  $sformatf("\n\t ----| 128 Weight: %d         \t ", key_128b_weight) };
    str = {str,  $sformatf("\n\t ----| 192 Weight: %d         \t ", key_192b_weight) };
    str = {str,  $sformatf("\n\t ----| 256 Weight: %d         \t ", key_256b_weight) };
    str = {str,  $sformatf("\n\t") };

    return str;
  endfunction // conver2string


  virtual function void do_copy(uvm_object rhs);
    aes_message_item rhs_;

    `downcast(rhs_,rhs)
    super.do_copy(rhs);
    aes_operation    = rhs_.aes_operation;
    aes_key          = rhs_.aes_key;
    aes_keylen       = rhs_.aes_keylen;
    aes_mode         = rhs_.aes_mode;
    aes_iv           = rhs_.aes_iv;
    message_length   = rhs_.message_length;
    has_config_error = rhs_.has_config_error;
    ecb_weight       = rhs_.ecb_weight;
    cbc_weight       = rhs_.cbc_weight;
    ctr_weight       = rhs_.ctr_weight;
    key_128b_weight  = rhs_.key_128b_weight;
    key_192b_weight  = rhs_.key_192b_weight;
    key_256b_weight  = rhs_.key_256b_weight;
    input_msg        = rhs_.input_msg;
    output_msg       = rhs_.output_msg;
    predicted_msg    = rhs_.predicted_msg;
  endfunction // copy
endclass
