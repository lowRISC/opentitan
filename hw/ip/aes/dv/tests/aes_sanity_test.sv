// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_sanity_test extends aes_base_test;

  `uvm_component_utils(aes_sanity_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);
     configure_env();
  endfunction

  function void configure_env();
     super.configure_env();
     cfg.errors_en          = 0;     // no errors in sanity test
     cfg.num_messages_min   = 2;
     cfg.num_messages_max   = 2;
     // message related knobs
     cfg.ecb_weight         = 100;   // only eCB
     cfg.cbc_weight         = 0;
     cfg.ctr_weight         = 0;
     cfg.message_len_min    = 16;    // one block (16bytes=128bits)
     cfg.message_len_max    = 16;    //

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
  endfunction
endclass : aes_sanity_test
