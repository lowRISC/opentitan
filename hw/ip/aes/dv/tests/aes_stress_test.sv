// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_stress_test extends aes_base_test;
  `uvm_component_utils(aes_stress_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     configure_env();
  endfunction

  virtual function void configure_env();
    //   cfg.ref_model          = OpenSSL;
    // env related knobs

    cfg.errors_en          = 0;
    cfg.num_messages_min   = 5;
    cfg.num_messages_max   = 5;
    // message related knobs
    cfg.ecb_weight         = 10;
    cfg.cbc_weight         = 40;
    cfg.ctr_weight         = 40;
    cfg.message_len_min    = 7;   // bytes
    cfg.message_len_max    = 251; // bytes
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_stress_test
