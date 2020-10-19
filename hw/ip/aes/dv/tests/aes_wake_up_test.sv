// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_wake_up_test extends aes_base_test;

  `uvm_component_utils(aes_wake_up_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     configure_env();
  endfunction

  virtual function void configure_env();
     cfg.en_scb             = 0;
     cfg.ecb_weight         = 100;
     cfg.cbc_weight         = 0;
     cfg.ctr_weight         = 0;
     cfg.num_messages_min   = 2;
     cfg.num_messages_max   = 2;
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_wake_up_test
