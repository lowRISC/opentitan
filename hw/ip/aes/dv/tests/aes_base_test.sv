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


  virtual function void configure_env();
    // cfg.ref_model          = OpenSSL;
    // env related knobs

    cfg.errors_en          = 0;
    cfg.num_messages_min   = 3;
    cfg.num_messages_max   = 3;
    // message related knobs
    cfg.ecb_weight         = 100;
    cfg.cbc_weight         = 0;
    cfg.ctr_weight         = 0;
    cfg.message_len_min    = 1;   // bytes
    cfg.message_len_max    = 599; // bytes
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction


endclass : aes_base_test
