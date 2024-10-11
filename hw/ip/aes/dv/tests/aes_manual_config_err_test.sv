// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_manual_config_err_test extends aes_base_test;

  `uvm_component_utils(aes_manual_config_err_test)
  `uvm_component_new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    configure_env();
  endfunction

  function void configure_env();
    super.configure_env();
    // disable scoreboard for this test
    cfg.en_scb                   = 0;
    cfg.error_types              = 4'b0001;
    // all should have error
    cfg.config_error_pct         = 100;
    // only allow mode errors
    cfg.config_error_type_en     = '{key_len:  1'b0,
                                     mode:     1'b1,
                                     rsd_rate: 1'b0,
                                     op:       1'b0};
    cfg.num_messages_min         = 1;
    cfg.num_messages_max         = 1;
    // message related knobs
    cfg.ecb_weight               = 10;
    cfg.cbc_weight               = 10;
    cfg.ctr_weight               = 10;
    cfg.ofb_weight               = 10;
    cfg.cfb_weight               = 10;

    cfg.message_len_min          = 16;
    cfg.message_len_max          = 128;
    cfg.manual_operation_pct     = 0;

    cfg.fixed_data_en            = 0;
    cfg.fixed_key_en             = 0;

    cfg.fixed_operation_en       = 0;

    cfg.fixed_keylen_en          = 0;

    cfg.fixed_iv_en              = 0;

    cfg.random_data_key_iv_order = 1;


    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_manual_config_err_test
