// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env_cfg extends cip_base_env_cfg #(.RAL_T(aes_reg_block));

  `uvm_object_utils_begin(aes_env_cfg)
  `uvm_object_utils_end
  `uvm_object_new

  // TODO sort knobs into test/SEQUENCE/message/item

  // test environment constraints //
  typedef enum { VerySlow, Slow, Fast, VeryFast } tl_ul_access_e;


    //  Message Knobs //
  int                num_messages_min            = 1;
  int                num_messages_max            = 1;
  int                message_len_min             = 128;
  int                message_len_max             = 128;
  bit                use_key_mask                = 0;
  bit                use_c_model_pct             = 0;

  // clear registers with 0's or rand
  bit                clear_reg_w_rand            = 1;
  // if set the order of which key iv and data is written will be randomized and interleaved
  bit                random_data_key_iv_order    = 1;

  // Mode distribution //
  // There are 5 modes (ecb, cbc, ofb, cfb, ctr). The weight for mode X is called X_weight. By
  // default, all weights are set equal at 10 (so each is selected 10/50 = 20% of the time).
  int                ecb_weight                 = 10;
  int                cbc_weight                 = 10;
  int                ofb_weight                 = 10;
  int                cfb_weight                 = 10;
  int                ctr_weight                 = 10;

  // KEYLEN weights
  // change of selecting 128b key
  //  128b/(128+192+256) = 10/30 = (33%)
  int                key_128b_weight            = 10;
  int                key_192b_weight            = 10;
  int                key_256b_weight            = 10;

  // use manual operation mode percentage
  int                manual_operation_pct       = 10;

  // debug / directed test knobs
  // use fixed key
  bit                fixed_key_en               = 0;
  // use fixed data (same data for each block in a message)
  bit                fixed_data_en              = 0;
  // fixed operation
  bit                fixed_operation_en         = 0;
  bit                fixed_operation            = 1'b0;
  // fixed iv (will set all to bits 0)
  bit                fixed_iv_en                = 0;

  bit                fixed_keylen_en            = 0;
  bit [2:0]          fixed_keylen               = 3'b001;


  //   [0]: configuration errors
  //   [1]: malicous injection
  //   [2]: random resets
  error_types_t      error_types                = 3'b111;

  //   [1]: mode error
  //   [0]: key_len
  cfg_error_type_t   config_error_type          = 2'b00;

  // number of messages that was selected to be corrupt
  // these should be excluded from the num_messages count
  // when checking that all messages was processed
  int                num_corrupt_messages       = 0;
  // percentage of configuration errors
  int                config_error_pct           = 10;
  int                mal_error_pct              = 5;
  int                random_reset_pct           = 10;

  // clear register percentage
  // percentage of items that will try to clear
  // one or more registers
  int                clear_reg_pct              = 0;

  // should the read vs write be unbalanced.
  bit                unbalanced = 0;
  // chance of reading valid output (for each status poll)
  int                read_prob = 80;
  // chance of writing data when DUT is ready (for each status poll)
  int                write_prob = 90;


  ///////////////////////////////
  // dont touch updated by env //
  ///////////////////////////////

  // keep track of how many packets was split
  int                split_cnt                  = 0;

  // rand variables
  // 0: C model 1: OPEN_SSL/BORING_SSL
  rand bit           ref_model;
  // randomly select if we force unused key bits to 0
  rand bit           key_mask;
  // number of messages to encrypt/decrypt
  rand int           num_messages;

  // TL UL contraints //
  rand tl_ul_access_e host_resp_speed;


  // constraints
  constraint c_num_messages {num_messages inside {[num_messages_min : num_messages_max]};}
  constraint c_ref_model    {ref_model    dist   { 0 :/ use_c_model_pct,
                                                    1 :/ (100 - use_c_model_pct)};}


  function void post_randomize();
    if (use_key_mask) key_mask = 1;

    case(host_resp_speed)
      VerySlow: begin
        m_tl_agent_cfg.d_ready_delay_min = 10;
        m_tl_agent_cfg.d_ready_delay_max = 10;
      end
      Slow: begin
        m_tl_agent_cfg.d_ready_delay_min = 4;
        m_tl_agent_cfg.d_ready_delay_max = 10;
      end
      Fast: begin
        m_tl_agent_cfg.d_ready_delay_min = 0;
        m_tl_agent_cfg.d_ready_delay_max = 5;
      end
      VeryFast: begin
        m_tl_agent_cfg.d_ready_delay_min = 0;
        m_tl_agent_cfg.d_ready_delay_max = 0;
      end
    endcase

    if (config_error_type[0] == 1'b1) num_corrupt_messages += 1;
  endfunction


  virtual function string convert2string();
    string str = "";
    str = super.convert2string();
    str = {str,  $sformatf("\n\t ----| AES ENVIRONMENT CONFIG \t ") };
    str = {str,  $sformatf("\n\t ----| Max Number of message %d \t ", num_messages_max)};
    str = {str,  $sformatf("\n\t ----| Min Number of message %d \t ", num_messages_min)};
    str = {str,  $sformatf("\n\t ----| Max message len %d bytes \t ", message_len_max)};
    str = {str,  $sformatf("\n\t ----| Min message len %d bytes \t ", message_len_min)};
    str = {str,  $sformatf("\n\t ----| Host response speed %s   \t ", host_resp_speed.name())};
    str = {str,  $sformatf("\n\t ----| Reference model:\t    %s              \t ",
         (ref_model==0) ? "C-MODEL" : "OPEN_SSL" )};
    str = {str,  $sformatf("\n\t ----| num_messages # %d \t ", num_messages)};
    str = {str,  $sformatf("\n\t ----| ECB Weight: %d         \t ", ecb_weight)};
    str = {str,  $sformatf("\n\t ----| CBC Weight: %d         \t ", cbc_weight)};
    str = {str,  $sformatf("\n\t ----| CFB Weight: %d         \t ", cfb_weight)};
    str = {str,  $sformatf("\n\t ----| OFB Weight: %d         \t ", ofb_weight)};
    str = {str,  $sformatf("\n\t ----| CTR Weight: %d         \t ", ctr_weight)};
    str = {str,  $sformatf("\n\t ----| key mask:   %b         \t ", key_mask)};
    str = {str, "\n"};
    return str;
  endfunction

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = aes_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
  endfunction

endclass
