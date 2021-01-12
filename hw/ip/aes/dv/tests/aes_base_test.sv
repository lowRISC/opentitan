// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_base_test extends cip_base_test #(
    .ENV_T(aes_env),
    .CFG_T(aes_env_cfg)
  );
  `uvm_component_utils(aes_base_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     configure_env();
   endfunction // build_phase

  //this will serve as the default setting.
  // overrides should happen in the specific testcase.
  virtual function void configure_env();


 // should the read vs write be unbalanced.
    cfg.unbalanced                  = 0;
    cfg.read_prob                   = 80;
    cfg.write_prob                  = 80;
    cfg.num_messages_min            = 1;
    cfg.num_messages_max            = 31;
    cfg.message_len_min             = 1;
    cfg.message_len_max             = 599;
    cfg.use_key_mask                = 0;
    cfg.use_c_model_pct             = 0;
    cfg.error_types                 = '0;
  // clear registers with 0's or rand
    cfg.clear_reg_w_rand            = 1;
  // if set the order of which key iv and data is written will be randomized and interleaved
    cfg.random_data_key_iv_order    = 1;

  // Mode distribution //
  // chance of selection ecb_mode
  // ecb_mode /(ecb_mode + cbc_mode + ctr_mode + cfb_mode + ofb_mode)
  // with the defaults 10/50 = 1/5 (20%)
    cfg.ecb_weight                 = 10;
    cfg.cbc_weight                 = 10;
    cfg.ofb_weight                 = 10;
    cfg.cfb_weight                 = 10;
    cfg.ctr_weight                 = 10;

  // KEYLEN weights
  // change of selecting 128b key
  //  128b/(128+192+256) = 10/30 = (33%)
    cfg.key_128b_weight            = 10;
    cfg.key_192b_weight            = 10;
    cfg.key_256b_weight            = 10;

  // use manual operation mode percentage
    cfg.manual_operation_pct       = 10;

  // debug / directed test knobs //
  // use fixed key
    cfg.fixed_key_en                = 0;
  // use fixed data (same data for each block in a message
    cfg.fixed_data_en               = 0;
  // fixed operation (enc or dec)
    cfg.fixed_operation_en          = 0;
    cfg.fixed_operation             = 1'b0;
  // fixed iv (will set all to 0)
    cfg.fixed_iv_en                 = 0;
    cfg.fixed_keylen_en             = 0;
    cfg.fixed_keylen                = 3'b001;

  //    1: error type enabled, 0: error type disabled
  //  001: configuration errors
  //  010: malicous injection
  //  100: random resets
    cfg.error_types                 = 3'b111;

    cfg.config_error_pct            = 0;           // percentage of configuration errors
  endfunction
endclass : aes_base_test
