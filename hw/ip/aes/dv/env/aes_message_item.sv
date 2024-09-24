// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_message_item extends uvm_sequence_item;

  `uvm_object_utils(aes_message_item)
  `uvm_object_new

  ///////////////////////////////////////
  //  control Knobs                    //
  ///////////////////////////////////////

  // min number of data bytes
  int               message_len_max       = 16;
  // Max number of data bytes
  int               message_len_min       = 1;
  // percentage of configuration errors
  int               config_error_pct      = 20;
  cfg_error_type_t  config_error_type_en  = '0;
  // errors enabled mask
  error_types_t     error_types           = 3'b000;

  // manual mode percentage
  int               manual_operation_pct  = 10;
  // maskout unused key bits
  bit               keymask               = 0;
  // use fixed key
  bit               fixed_key_en          = 0;
  // used fixed key length
  bit               fixed_keylen_en       = 0;
  // use fixed data (same data for each block in a message
  bit               fixed_data_en         = 0;
  // fixed operation
  bit               fixed_operation_en    = 0;
  // fixed IV
  bit               fixed_iv_en           = 0;
  // sideload
  int               sideload_pct          = 0;
  rand bit          sideload_en           = 0;

  // clear register percentage
  // percentage of items that will try to clear
  // one or more registers
  int               clear_reg_pct         = 0;


  // predefined values for fixed mode
  bit [3:0] [31:0]    fixed_data       = 128'hDEADBEEFEEDDBBAABAADBEEFDEAFBEAD;
  bit [7:0] [31:0]    fixed_key [2]    = '{256'h0000111122223333444455556666777788889999AAAABBBBCCCCDDDDEEEEFFFF, 256'h0};
  bit [2:0]           fixed_keylen     = 3'b001;
  bit [1:0]           fixed_operation  = AES_ENC;
  bit [3:0] [31:0]    fixed_iv         = 128'h00000000000000000000000000000000;

  // Mode distribution //
  // chance of selection ecb_mode
  // ecb_mode /(ecb_mode + cbc_mode + cfb_mode + ofb_mode + ctr_mode)
  // with the defaults 10/50 = 1/5 (20%)
  int    ecb_weight           = 10;
  int    cbc_weight           = 10;
  int    cfb_weight           = 10;
  int    ofb_weight           = 10;
  int    ctr_weight           = 10;

  // KEYLEN weights
  int    key_128b_weight      = 10;
  int    key_192b_weight      = 10;
  int    key_256b_weight      = 10;

  // reseed weight
  int    per1_weight          = 60;
  int    per64_weight         = 30;
  int    per8k_weight         = 10;

  // set if this message should not be
  // validated
  // due to a premature trigger
  // i.e unkown key and IV settings used
  bit    skip_msg             = 0;

  ///////////////////////////////////////
  // Randomizable variables            //
  ///////////////////////////////////////

  // length of the message                                     //
  rand int               message_length;
  // mode - which type of ecnryption is used                   //
  rand aes_mode_e        aes_mode = AES_NONE;
  // operation - encruption or decryption                      //
  rand bit [1:0]         aes_operation;
  // aes key length                                            //
  rand bit [2:0]         aes_keylen;
  // 256 bit key (8x32 bit)                                    //
  rand bit [7:0][31:0]   aes_key [2];
  // 256 bit initialization vector (8x32 bit)                  //
  rand bit [3:0][31:0]   aes_iv;
  // configuration error                                       //
  rand bit               has_config_error;
  // [0]: op_error
  // [1]: reseed error
  // [2]: mode error
  // [3]: key_len
  rand cfg_error_type_t  cfg_error_type;
  // run AES in manual mode
  rand bit               manual_operation;
  // reseed rate
  rand bit [2:0]         reseed_rate;


  ///////////////////////////////////////
  // FIXED variables                   //
  ///////////////////////////////////////

  bit [7:0]            input_msg[];
  bit [7:0]            output_msg[];
  bit [7:0]            predicted_msg[];
  bit                  output_cleared[];

  ///////////////////////////////////////
  // Constraints                       //
  ///////////////////////////////////////

  constraint data_c { message_length inside { [message_len_min:message_len_max] };}

  constraint has_config_error_c {
    if (error_types.cfg) {
      has_config_error dist { 0 :/ (100 - config_error_pct),
                              1 :/ config_error_pct};
    } else {
      has_config_error == 0;
    }
  }

  constraint config_error_type_c {
    solve has_config_error before cfg_error_type;
    if (has_config_error) {
      cfg_error_type inside {[1:15]};
      config_error_type_en.op       == 0 -> cfg_error_type.op       == 0;
      config_error_type_en.rsd_rate == 0 -> cfg_error_type.rsd_rate == 0;
      config_error_type_en.mode     == 0 -> cfg_error_type.mode     == 0;
      config_error_type_en.key_len  == 0 -> cfg_error_type.key_len  == 0;
    } else {
      cfg_error_type == '0;
    }
  }

  constraint keylen_c {
    solve has_config_error before aes_keylen;
    solve cfg_error_type before aes_keylen;
    if (!(has_config_error && cfg_error_type.key_len) ) {
      aes_keylen inside { AES_128, AES_192, AES_256 };
      aes_keylen dist   { AES_128 := key_128b_weight,
                          AES_192 := key_192b_weight,
                          AES_256 := key_256b_weight };
    } else {
      !(aes_keylen inside { AES_128, AES_192, AES_256 });
    }
    // A fixed key length is given the highest priority. This setting is mostly useful for
    // debugging the DUT.
    if (fixed_keylen_en) {
      aes_keylen == fixed_keylen
    };
  }

  constraint mode_c {
    solve has_config_error before aes_mode;
    solve cfg_error_type before aes_mode;
    if (!(has_config_error && cfg_error_type.mode)) {
      aes_mode dist   { AES_ECB := ecb_weight,
                        AES_CBC := cbc_weight,
                        AES_CFB := cfb_weight,
                        AES_OFB := ofb_weight,
                        AES_CTR := ctr_weight};
    } else {
      // the mode will be randomized to a random
      // non legal value later.
      aes_mode == AES_NONE;
    }
  }

  constraint rsd_rate_c {
    solve has_config_error before reseed_rate;
    solve cfg_error_type before reseed_rate;
    if (!(has_config_error && cfg_error_type.rsd_rate) ) {
      reseed_rate inside { PER_1, PER_64, PER_8K };
      reseed_rate dist   { PER_1  :/ per1_weight,
                           PER_64 :/ per64_weight,
                           PER_8K :/ per8k_weight };
    } else {
      !( reseed_rate  inside { PER_1, PER_64, PER_8K });
    }
  }

  constraint operation_c {
    solve has_config_error before aes_operation;
    solve cfg_error_type before aes_operation;
    if (!(has_config_error && cfg_error_type.op) ) {
      aes_operation inside { AES_ENC, AES_DEC };
      aes_operation dist   { AES_ENC :/ 1,
                             AES_DEC :/ 1 };
    } else {
      !( aes_operation inside { AES_ENC, AES_DEC });
    }
    // A fixed operation is given the highest priority. This setting is mostly useful for
    // debugging the DUT.
    if (fixed_operation_en) {
      aes_operation == fixed_operation
    };
  }

  constraint key_c {
    if (fixed_key_en) {
      aes_key[0] == fixed_key[0],
      aes_key[1] == fixed_key[1]
    };
  }

  constraint iv_c {
    if (fixed_iv_en) {
      aes_iv == fixed_iv
    };
  }

  constraint sideload_c {
    sideload_en dist{ 0:/(100-sideload_pct),
                      1:/sideload_pct};
  }

  constraint manual_operation_c {
    solve sideload_en before manual_operation;
    if (!sideload_en) {
      manual_operation dist { 0:/ (100 - manual_operation_pct),
                              1:/ manual_operation_pct};
    } else {
      manual_operation == 0 ;
    }
  }

  function void add_data_item(aes_seq_item item);
    for (int i=0; i < 4 ; i++) begin
      input_msg  = { input_msg , item.data_in[i][7:0], item.data_in[i][15:8], item.data_in[i][23:16]
                    ,item.data_in[i][31:24]};
      output_msg = { output_msg, item.data_out[i][7:0], item.data_out[i][15:8],
                     item.data_out[i][23:16],item.data_out[i][31:24] };
      `uvm_info(`gfn, $sformatf("\n\t ---| adding to 0x%0h to data, length is now: %0d",
               {item.data_in[i][7:0], item.data_in[i][15:8],item.data_in[i][23:16], item.data_in[i][31:24]},
               input_msg.size()), UVM_FULL)
      output_cleared = { output_cleared, item.data_was_cleared, item.data_was_cleared,
                        item.data_was_cleared, item.data_was_cleared};
    end
  endfunction // add_data_item


  function void add_start_msg_item(aes_seq_item item);
    this.aes_mode      = item.mode;
    this.aes_operation = item.operation;
    this.aes_key       = item.key;
    this.aes_iv        = item.iv;
    this.reseed_rate   = item.reseed_rate;

    // Check for invalid configuration values and resolve them if necessary. Illegal mode values
    // don't need to be handled here as they don't result in the DUT actually producing output
    // data.
    if (item.operation inside {AES_ENC, AES_DEC}) begin
      this.aes_operation = item.operation;
    end else begin
      this.aes_operation = AES_ENC;
      `uvm_info(`gfn,
          $sformatf("\n\t ---| Illegal operation value detected. Resolving to default AES_ENC"),
          UVM_MEDIUM)
    end
    if (item.key_len inside {AES_128, AES_192, AES_256}) begin
      this.aes_keylen = item.key_len;
    end else begin
      this.aes_keylen = AES_256;
      `uvm_info(`gfn,
          $sformatf("\n\t ---| Illegal key length value detected. Resolving to default AES_256"),
          UVM_MEDIUM)
    end
    if (item.reseed_rate inside {PER_1, PER_64, PER_8K}) begin
      this.reseed_rate = item.reseed_rate;
    end else begin
      this.reseed_rate = PER_1;
      `uvm_info(`gfn,
          $sformatf("\n\t ---| Illegal reseed rate value detected. Resolving to default PER_1"),
          UVM_MEDIUM)
    end
    add_data_item(item);
  endfunction // add_start_msg_item


  function void alloc_predicted_msg();
    predicted_msg = new[input_msg.size()];
  endfunction // alloc_predicted_msg


  // convert to string //
  virtual function string convert2string();
    string str;
    str = super.convert2string();
    str = {str,  $sformatf("\n\t ----| \t\t AES MESSAGE ITEM   \t      |----\t ")
           };
    str = {str, "\n\t ----| "};
    str = {str,  $sformatf("\n\t ----| Mode: \t  \t \t %s                         \t ",
                           aes_mode.name())};
    str = {str,  $sformatf("\n\t ----| Operation:            %s",
                           aes_operation == AES_ENC ? "AES_ENC" :
                           aes_operation == AES_DEC ? "AES_DEC" : "INVALID")};
    str = {str,  $sformatf("\n\t ----| has Configuration error:  %s  \t  \t        \t ",
                           (has_config_error==1) ? "TRUE" : "FALSE")};
    str = {str,  $sformatf("\n\t ----| Mode error en:  \t %d \n\t ----| Key_len error en: \t %d  \t         \t ",
                           cfg_error_type.mode, cfg_error_type.key_len)};
    str = {str,  $sformatf("\n\t ----| Message Length:  \t  \t %d             \t ",
                           message_length)};

    str = {str,  $sformatf("\n\t ----| Key Length:   \t \t %03b                             \t ",
                           aes_keylen)};
    str = {str,  $sformatf("\n\t ----| Key Share 0: \t \t ")};
    for (int i=0; i <8; i++) begin
      str = {str, $sformatf("%h ",aes_key[0][i])};
    end
    str = {str,  $sformatf("\n\t ----| Key Share 1: \t \t ")};
    for (int i=0; i <8; i++) begin
      str = {str, $sformatf("%h ",aes_key[1][i])};
    end
    str = {str,  $sformatf("\n\t ----| Key Mask:  \t  \t %0b                             |----\t ",
                           keymask)};
     str = {str,  $sformatf("\n\t ----| Initializaion vector:     \t    \t ")};
    for (int i=0; i <4; i++) begin
      str = {str, $sformatf("%h ",aes_iv[i])};
    end
    str = {str,  $sformatf("\n\t ----| Manual Mode : %b      \t   \t ", manual_operation)};
    str = {str,  $sformatf("\n\t ----| SideLoad En : %b      \t   \t ", sideload_en)};
    str = {str,  $sformatf("\n\t ----| errors types enabled: %b      \t   \t ", error_types)};
    str = {str,  $sformatf("\n\t ----| CFB Weight: %d       \t \t ", cfb_weight)};
    str = {str,  $sformatf("\n\t ----| OFB Weight: %d       \t \t ", ofb_weight)};
    str = {str,  $sformatf("\n\t ----| ECB Weight: %d       \t \t ", ecb_weight)};
    str = {str,  $sformatf("\n\t ----| CBC Weight: %d       \t \t ", cbc_weight)};
    str = {str,  $sformatf("\n\t ----| CTR Weight: %d       \t \t ", ctr_weight)};
    str = {str,  $sformatf("\n\t ----| Key Len Distribution: \t \t " ) };
    str = {str,  $sformatf("\n\t ----| 128 Weight: %d       \t \t ", key_128b_weight)};
    str = {str,  $sformatf("\n\t ----| 192 Weight: %d       \t \t ", key_192b_weight)};
    str = {str,  $sformatf("\n\t ----| 256 Weight: %d       \t \t ", key_256b_weight)};
    str = {str,  $sformatf("\n\t")};

    return str;
  endfunction // conver2string

   virtual function string print_data();
     string txt="";

     txt = $sformatf("\n\t ---| Printing message data \n\t ---| data length: %d", input_msg.size());
     foreach (input_msg[i]) begin
       txt = {txt, $sformatf("\n\t ----| [%0d] 0x%0h \t 0x%0h",i, input_msg[i], output_msg[i])};
     end
     return txt;
   endfunction // get_data_length


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
    cfg_error_type   = rhs_.cfg_error_type;
    error_types      = rhs_.error_types;
    ecb_weight       = rhs_.ecb_weight;
    cbc_weight       = rhs_.cbc_weight;
    cfb_weight       = rhs_.cfb_weight;
    ofb_weight       = rhs_.ofb_weight;
    ctr_weight       = rhs_.ctr_weight;
    key_128b_weight  = rhs_.key_128b_weight;
    key_192b_weight  = rhs_.key_192b_weight;
    key_256b_weight  = rhs_.key_256b_weight;
    input_msg        = rhs_.input_msg;
    output_msg       = rhs_.output_msg;
    output_cleared   = rhs_.output_cleared;
    predicted_msg    = rhs_.predicted_msg;
    manual_operation = rhs_.manual_operation;
    keymask          = rhs_.keymask;
    fixed_data_en    = rhs_.fixed_data_en;
    fixed_data       = rhs_.fixed_data;
    fixed_iv_en      = rhs_.fixed_iv_en;
    skip_msg         = rhs_.skip_msg;
    sideload_en      = rhs_.sideload_en;
    reseed_rate      = rhs_.reseed_rate;
  endfunction // copy
endclass
