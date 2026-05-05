// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_alert_test extends csrng_base_test;

  `uvm_component_utils(csrng_alert_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                          = 0;
    cfg.otp_en_cs_sw_app_read_pct       = 100;
    cfg.otp_en_cs_sw_app_read_inval_pct = 0;
    cfg.sw_app_enable_pct               = 100;
    cfg.use_invalid_mubi                = 1;
  endfunction
endclass : csrng_alert_test
