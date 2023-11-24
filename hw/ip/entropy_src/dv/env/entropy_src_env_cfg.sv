// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env_cfg extends cip_base_env_cfg #(.RAL_T(entropy_src_reg_block));

  `uvm_object_utils(entropy_src_env_cfg)
  `uvm_object_new

  // Ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(RNG_BUS_WIDTH))
       m_rng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))
       m_csrng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(0))
       m_aes_halt_agent_cfg;
  entropy_src_xht_agent_cfg m_xht_agent_cfg;

  // Additional reset interface for the csrng.
  virtual clk_rst_if    csrng_rst_vif;
  virtual pins_if#(8)   otp_en_es_fw_read_vif;
  virtual pins_if#(8)   otp_en_es_fw_over_vif;

  // Configuration for DUT CSRs (held in a separate object for easy re-randomization)
  entropy_src_dut_cfg dut_cfg;

  // handle to entropy_src assert interface
  virtual entropy_src_assert_if entropy_src_assert_vif;
  // handle to entropy_src path interface
  virtual entropy_src_path_if   entropy_src_path_vif;

  // handle to the interrupt interface
  dv_utils_pkg::intr_vif interrupt_vif;
  // Pointer to the preconditioning and bypass fifo exception interfaces.
  // (For tracking errors during FW_OV mode)
  virtual entropy_subsys_fifo_exception_if#(1) precon_fifo_vif;
  virtual entropy_subsys_fifo_exception_if#(1) bypass_fifo_vif;

  // Pointer to the FSM state tracking interface.
  // (Coverage completion requires earlier notice of following state).
  virtual entropy_src_fsm_cov_if fsm_tracking_vif;

  //
  // Variables for controlling test duration.  Depending on the test there are two options:
  // fixed duration in time or total number of seeds.
  //
  // When selecting fixed duration, the total simulated duration of the test is approximately
  // equal to cfg.sim_duration
  //
  // TODO(#18836): Randomize & constrain the following values.
  realtime sim_duration;

  // Mean time before hard RNG failure
  realtime hard_mtbf;
  // Mean time before "soft" RNG failure (still functions but less entropy per bit)
  realtime soft_mtbf;

  // Mean time between unexpected configuration update events
  // Default: Negative, meaning no random reconfigs
  realtime mean_rand_reconfig_time = -1;

  // Mean time ERR_CODE_TEST CSR-driven alert events
  // Default: Negative, meaning no random reconfigs
  realtime mean_rand_csr_alert_time = -1;

  // Maximum time to wait for non-seed generating DUT configurations
  realtime max_silent_reconfig_time = -1;

  // Time to pause between register configs.
  realtime configuration_pause_time = 0ns;

  int      seed_cnt;

  // The AST/RNG does not pay attention to the entropy_src `ready` backpressure signal on the RNG
  // entropy_src interface.  We mimic this behavior in the RNG and FW_OV tests, which expect random
  // RNG data.  For other tests (which rely on fixed RNG sequences) we leave handshaking enabled.
  bit      rng_ignores_backpressure = 0;


  /////////////////////
  // Knobs & Weights //
  /////////////////////

  // Knob to inject entropy even if the DUT is configured to not accept it
  uint          spurious_inject_entropy_pct;

  // Constraint knobs for OTP-driven inputs
  uint          otp_en_es_fw_read_pct, otp_en_es_fw_read_inval_pct,
                otp_en_es_fw_over_pct, otp_en_es_fw_over_inval_pct;

  // Behavioral constrint knob: dictates how often each sequence
  // performs a survey of the health test diagnostics.
  // (100% corresponds to a full diagnostic chack after every HT alert,
  // If less than 100%, this full-diagnostic is skipped after some alerts)
  uint          do_check_ht_diag_pct;

  // Constraint knob to limit how often the RNG vseq forces a yet-unseen FSM transition
  uint          induce_targeted_transition_pct;

  /////////////////////////////////////////////////////////////////
  // Implementation-specific constants related to the DUT        //
  // (Needed for accurate prediction, no randomization required) //
  /////////////////////////////////////////////////////////////////

  // Number of clock cycles between a TLUL disable signal, and deassertion
  // of enable on the RNG bus.

  int tlul_to_rng_disable_delay = 0;
  int tlul_to_fifo_clr_delay    = 5;

  // When expecting an alert, the cip scoreboarding routines expect a to see the
  // alert within alert_max_delay clock cycles.
  int      alert_max_delay;

  // Whether to keep the default response on the XHT interface at all time.
  bit xht_only_default_rsp = 1;

  ///////////////////////
  // Randomized fields //
  ///////////////////////

  // OTP variables.
  rand logic [7:0]              otp_en_es_fw_read, otp_en_es_fw_over;

  rand bit                      spurious_inject_entropy;

  // Random values for interrupt, alert and error tests
  rand fatal_err_e      which_fatal_err;
  rand err_code_e       which_err_code;
  rand which_fifo_e     which_fifo;
  rand which_fifo_err_e which_fifo_err;
  rand ht_fail_e        which_ht_fail;
  rand cntr_e           which_cntr;
  rand which_ht_e       which_ht;

  rand uint  which_cntr_replicate;

  rand uint  which_bin;

  rand bit   induce_targeted_transition;

  /////////////////
  // Constraints //
  /////////////////

  constraint otp_en_es_fw_read_c {
    `DV_MUBI8_DIST(otp_en_es_fw_read, otp_en_es_fw_read_pct,
                                      100 - otp_en_es_fw_read_pct - otp_en_es_fw_read_inval_pct,
                                      otp_en_es_fw_read_inval_pct)
  }

  constraint otp_en_es_fw_over_c {
    `DV_MUBI8_DIST(otp_en_es_fw_over, otp_en_es_fw_over_pct,
                                      100 - otp_en_es_fw_over_pct - otp_en_es_fw_over_inval_pct,
                                      otp_en_es_fw_over_inval_pct)
  }

  constraint spurious_inject_entropy_c {spurious_inject_entropy dist {
      1                         :/ spurious_inject_entropy_pct,
      0                         :/ (100 - spurious_inject_entropy_pct) };}

  // Scale the frequency of each error code with the number of sub cover points (number of counters
  // etc)
  // Let the RNG test manage the CSR-driven errors
  constraint which_err_code_c {
    which_err_code dist {
      sfifo_esrng_err   :/ 2,
      sfifo_observe_err :/ 3,
      sfifo_esfinal_err :/ 2,
      es_ack_sm_err     :/ 2,
      es_main_sm_err    :/ 2,
      es_cntr_err       :/ 60,
      fifo_write_err    :/ 2,
      fifo_read_err     :/ 3,
      fifo_state_err    :/ 3};}

  constraint which_cntr_replicate_c {which_cntr_replicate inside {[0:RNG_BUS_WIDTH-1]};}
  int        num_bins = 2**RNG_BUS_WIDTH;
  constraint which_bin_c {which_bin inside {[0:num_bins-1]};}

  // Choose the counter to probe by the number of bins or channels with each counter
  constraint which_cntr_c {which_cntr dist {
    window_cntr     :/ 1,
    repcnt_ht_cntr  :/ 4,
    repcnts_ht_cntr :/ 1,
    adaptp_ht_cntr  :/ 4,
    bucket_ht_cntr  :/ 16,
    markov_ht_cntr  :/ 4};}

  // Write errors no longer apply to the esfinal or esrng fifos
  // so exclude those combinations when targetting a specific fifo or error condition
  constraint which_fifo_err_c {
    which_err_code inside {sfifo_esrng_err, sfifo_esfinal_err} ->
      which_fifo_err inside {read, state};
    which_err_code == fifo_write_err -> which_fifo_err == write;
    which_err_code == fifo_read_err -> which_fifo_err == read;
    which_err_code == fifo_state_err -> which_fifo_err == state;
  }

  constraint which_fifo_c {
    which_err_code == fifo_write_err -> which_fifo == sfifo_observe;
    which_err_code == sfifo_observe_err -> which_fifo == sfifo_observe;
    which_err_code == sfifo_esrng_err -> which_fifo == sfifo_esrng;
    which_err_code == sfifo_esfinal_err -> which_fifo == sfifo_esfinal;
  }

  constraint induce_targeted_transition_c {induce_targeted_transition dist {
    1                         :/ induce_targeted_transition_pct,
    0                         :/ (100 - induce_targeted_transition_pct) };}

  ///////////////
  // Functions //
  ///////////////

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    dut_cfg = entropy_src_dut_cfg::type_id::create("dut_cfg");

    // create agent config objs
    m_rng_agent_cfg       = push_pull_agent_cfg#(.HostDataWidth(RNG_BUS_WIDTH))::
                            type_id::create("m_rng_agent_cfg");
    m_csrng_agent_cfg     = push_pull_agent_cfg#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))::
                            type_id::create("m_csrng_agent_cfg");
    m_aes_halt_agent_cfg  = push_pull_agent_cfg#(.HostDataWidth(0))::
                            type_id::create("m_aes_halt_agent_cfg");
    m_xht_agent_cfg       = entropy_src_xht_agent_cfg::type_id::create("m_xht_agent_cfg");

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    // get entropy_src assert interface handle
    if (!uvm_config_db#(virtual entropy_src_assert_if)::
        get(null, "*.env" , "entropy_src_assert_vif", entropy_src_assert_vif)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ASSERT IF"))
    end

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;

    // Disable random CDC delays in alert sender because the scoreboard otherwise could not
    // accurately predict whether an alert request gets merged with an outstanding request or not
    // (#18796).
    disabled_prim_cdc_rand_delays = new[2];
    foreach (disabled_prim_cdc_rand_delays[i]) begin
     string path = "tb.dut.gen_alert_tx[0].u_prim_alert_sender.u_decode_ack.gen_async";
     unique case (i)
       0: path = {path, ".i_sync_n"};
       1: path = {path, ".i_sync_p"};
     endcase
     disabled_prim_cdc_rand_delays[i] = {path, ".u_prim_cdc_rand_delay"};
    end
  endfunction

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str, "\n\t |**************** entropy_src_env_cfg *****************| \t"};

    str = {
        str,
        $sformatf("\n\t |***** otp_en_es_fw_read           :         'h%02h *****| \t",
                  otp_en_es_fw_read),
        $sformatf("\n\t |***** otp_en_es_fw_over           :         'h%02h *****| \t",
                  otp_en_es_fw_over),
        $sformatf("\n\t |***** seed_cnt                    : %12d *****| \t",
                  seed_cnt),
        $sformatf("\n\t |***** sim_duration                : %9.2f ms *****| \t",
                  sim_duration/1ms)
    };

    str = {str, "\n\t |----------------- knobs ------------------------------| \t"};

    str = {
        str,
        $sformatf("\n\t |***** otp_en_es_fw_read_pct       : %12d *****| \t",
                  otp_en_es_fw_read_pct),
        $sformatf("\n\t |***** otp_en_es_fw_read_inval_pct : %12d *****| \t",
                  otp_en_es_fw_read_inval_pct),
        $sformatf("\n\t |***** otp_en_es_fw_over_pct       : %12d *****| \t",
                  otp_en_es_fw_over_pct),
        $sformatf("\n\t |***** otp_en_es_fw_over_inval_pct : %12d *****| \t",
                  otp_en_es_fw_over_inval_pct)
    };

    str = {str, "\n\t |******************************************************| \t"};
    str = {str, dut_cfg.convert2string()};

    return str;
  endfunction

  function void post_randomize();
    void'(dut_cfg.randomize());
    super.post_randomize();
  endfunction

  function void pre_randomize();
    check_knob_vals();
    super.pre_randomize();
  endfunction

  function void check_knob_vals();
    `DV_CHECK(spurious_inject_entropy_pct <= 100);
    `DV_CHECK(otp_en_es_fw_read_pct <= 100);
    `DV_CHECK(otp_en_es_fw_read_inval_pct <= 100);
    `DV_CHECK((otp_en_es_fw_read_pct + otp_en_es_fw_read_inval_pct) <= 100);
    `DV_CHECK(otp_en_es_fw_over_inval_pct <= 100);
    `DV_CHECK((otp_en_es_fw_over_pct + otp_en_es_fw_over_inval_pct) <= 100);
    `DV_CHECK(otp_en_es_fw_over_pct <= 100);
    `DV_CHECK(do_check_ht_diag_pct <= 100);
    `DV_CHECK(induce_targeted_transition_pct <= 100);
  endfunction

  // Some combinations of environment and DUT configurations do not generate seeds. This function
  // helps vseqs identify these inactive configurations to more quickly prompt a reconfiguration
  // to get more coverage in a given run.
  function bit generates_seeds(mubi4_t route_software, mubi4_t entropy_data_reg_enable);
    if (route_software == MuBi4True) begin
      return (otp_en_es_fw_read == MuBi8True) && (entropy_data_reg_enable == MuBi4True);
    end
    return 1;
  endfunction

  // Similar to generates_seeds(), returns true if a configuration should be able to
  // generate observe_data
  function bit generates_observe_data(mubi4_t fw_read_enable);
     return (otp_en_es_fw_over == MuBi8True) && (fw_read_enable == MuBi4True);
  endfunction

endclass
