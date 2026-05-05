// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_test extends cip_base_test #(
    .CFG_T(csrng_env_cfg),
    .ENV_T(csrng_env)
  );

  `uvm_component_utils(csrng_base_test)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  // A function defined in dv_base_test
  //
  // In this extended class, we set the shape of the environment (by calling set_num_hw_apps) before
  // the base class calls cfg.initialize(), and then follow-up by calling configure_env.
  virtual function void initialize_env_cfg();
    int unsigned num_hw_apps;

    if (!uvm_config_db#(int unsigned)::get(this, "", "num_hw_apps", num_hw_apps)) begin
      `uvm_fatal(get_full_name(), "Failed to get num_hw_apps from uvm_config_db.")
    end
    cfg.set_num_hw_apps(num_hw_apps);

    super.initialize_env_cfg();

    configure_env();
  endfunction

  virtual function void configure_env();
    cfg.otp_en_cs_sw_app_read_pct        = 80;
    cfg.otp_en_cs_sw_app_read_inval_pct  = 10;
    cfg.lc_hw_debug_en_pct               = 50;
    cfg.regwen_pct                       = 100;
    cfg.enable_pct                       = 100;
    cfg.sw_app_enable_pct                = 90;
    cfg.read_int_state_pct               = 95;
    cfg.fips_force_enable_pct            = 50;
    cfg.check_int_state_pct              = 100;
    cfg.int_state_read_enable_pct        = 95;
    cfg.int_state_read_enable_regwen_pct = 50;
  endfunction

endclass : csrng_base_test
