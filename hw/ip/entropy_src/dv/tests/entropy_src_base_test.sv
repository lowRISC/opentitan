// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_test extends cip_base_test #(
    .CFG_T(entropy_src_env_cfg),
    .ENV_T(entropy_src_env)
  );

  `uvm_component_utils(entropy_src_base_test)
  `uvm_component_new

   virtual function void build_phase(uvm_phase phase);
     super.build_phase(phase);

     configure_env();
   endfunction // build_phase

  // the base class dv_base_test creates the following instances:
  // entropy_src_env_cfg: cfg
  // entropy_src_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  // The following knob settings will serve as the defaults.
  // Overrides should happen in the specific testcase.

  virtual function void configure_env();
    // Take plusargs into account.
    int rng_max_delay;
    bit xht_only_default_rsp;
    if ($value$plusargs("rng_max_delay=%0d", rng_max_delay)) begin
      `uvm_info(`gfn, $sformatf("+rng_max_delay specified"), UVM_MEDIUM)
      cfg.rng_max_delay = rng_max_delay;
    end
    if ($value$plusargs("xht_only_default_rsp=%0b", xht_only_default_rsp)) begin
      `uvm_info(`gfn, $sformatf("+xht_only_default_rsp specified"), UVM_MEDIUM)
      cfg.xht_only_default_rsp = xht_only_default_rsp;
    end

    cfg.rng_ignores_backpressure       = 0;
    cfg.otp_en_es_fw_read_pct          = 100;
    cfg.otp_en_es_fw_read_inval_pct    = 0;
    cfg.otp_en_es_fw_over_pct          = 100;
    cfg.otp_en_es_fw_over_inval_pct    = 0;
    cfg.dut_cfg.en_intr_pct            = 75;
    cfg.dut_cfg.me_regwen_pct          = 100;
    cfg.dut_cfg.sw_regupd_pct          = 100;

    cfg.dut_cfg.module_enable_pct      = 100;
    cfg.dut_cfg.type_bypass_pct        = 100;
    cfg.dut_cfg.preconfig_disable_pct  = 100;
    cfg.dut_cfg.fips_flag_pct          = 75;
    cfg.dut_cfg.rng_fips_pct           = 75;
    // Unless testing bad MuBi's the initial value for fw_ov_insert_start should always be false
    cfg.dut_cfg.fw_ov_insert_start_pct = 0;

    // Setting the following parameters to less than zero means that random reconfig or random
    // fatal alerts will not be driven by the RNG virtual sequence unless they are overridden
    // in one of the derived test classes.
    cfg.mean_rand_reconfig_time   = -1.0;
    cfg.mean_rand_csr_alert_time  = -1.0;
    cfg.max_silent_reconfig_time  = -1.0;
    cfg.soft_mtbf                 = -1.0;
    cfg.hard_mtbf                 = -1.0;

    cfg.dut_cfg.bad_mubi_cfg_pct       = 0;
    cfg.induce_targeted_transition_pct = 0;
    cfg.dut_cfg.tight_thresholds_pct   = 0;

    // Set the maximum threshold for the observe FIFO threshold randomization to ObserveFifoDepth.
    cfg.dut_cfg.max_observe_fifo_threshold = entropy_src_reg_pkg::ObserveFifoDepth;

  endfunction

endclass : entropy_src_base_test
