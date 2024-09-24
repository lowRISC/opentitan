// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_fi_test extends aes_base_test;

  `uvm_component_utils(aes_fi_test)
  `uvm_component_new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    configure_env();
  endfunction

  function void configure_env();
    super.configure_env();
    cfg.en_scb                   = 0;
    cfg.error_types              = 4'b1110; // inject errors in regs and fsm errors
    cfg.num_messages_min         = 3;
    cfg.num_messages_max         = 6;
    cfg.unbalanced               = 0;
    // message related knobs
    cfg.ecb_weight               = 5;
    cfg.cbc_weight               = 5;
    cfg.ofb_weight               = 5;
    cfg.cfb_weight               = 5;
    cfg.ctr_weight               = 80;

    cfg.message_len_min          = 1;    // one block (16bytes=128bits)
    cfg.message_len_max          = 65;
    cfg.manual_operation_pct     = 0;
    cfg.use_key_mask             = 0;

    cfg.fixed_data_en            = 0;
    cfg.fixed_key_en             = 0;

    cfg.fixed_operation_en       = 0;
    cfg.fixed_operation          = aes_pkg::AES_ENC;

    cfg.fixed_keylen_en          = 0;
    cfg.fixed_keylen             = 3'b001;

    cfg.fixed_iv_en              = 0;

    cfg.random_data_key_iv_order = 1;
    cfg.read_prob                = 70;
    cfg.write_prob               = 90;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_fi_test
