// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_deinit_test extends aes_base_test;

  `uvm_component_utils(aes_deinit_test)
  `uvm_component_new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    configure_env();
  endfunction

  function void configure_env();
    super.configure_env();
    // disable scoreboard for this test
    cfg.en_scb                   = 0;
    cfg.error_types              = 0;     // no errors in smoke test
    cfg.num_messages_min         = 1;
    cfg.num_messages_max         = 5;
    // message related knobs
    cfg.ecb_weight               = 10;
    cfg.cbc_weight               = 10;
    cfg.ctr_weight               = 10;
    cfg.ofb_weight               = 10;
    cfg.cfb_weight               = 10;

    cfg.message_len_min          = 16;    // one block (16bytes=128bits)
    cfg.message_len_max          = 128;  //
    cfg.manual_operation_pct     = 0;

    cfg.fixed_data_en            = 0;
    cfg.fixed_key_en             = 0;

    cfg.fixed_operation_en       = 0;

    cfg.fixed_keylen_en          = 0;

    cfg.fixed_iv_en              = 0;

    cfg.random_data_key_iv_order = 1;


    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_deinit_test
