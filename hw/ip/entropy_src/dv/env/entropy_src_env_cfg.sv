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
  intr_vif interrupt_vif;
  // Pointer to the preconditioning fifo exception interface.
  // (For tracking errors during FW_OV mode)
  virtual entropy_subsys_fifo_exception_if#(1) precon_fifo_vif;

  //
  // Variables for controlling test duration.  Depending on the test there are two options:
  // fixed duration in time or total number of seeds.
  //
  // When selecting fixed duration, the total simulated duration of the test is approximately
  // equal to cfg.sim_duration
  //
  // TODO: Randomize & constrain the following values
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

  int      seed_cnt;

  /////////////////////
  // Knobs & Weights //
  /////////////////////

  // Knob to inject entropy even if the DUT is configured to not accept it
  uint          spurious_inject_entropy_pct;

  // Constraint knobs for OTP-driven inputs
  uint          otp_en_es_fw_read_pct, otp_en_es_fw_over_pct;

  // Behavioral constrint knob: dictates how often each sequence
  // performs a seurvey of the health test diagnostics.
  // (100% corresponds to a full diagnostic chack after every HT alert,
  // If less than 100%, this full-diagnostic is skipped after some alerts)
  uint          do_check_ht_diag_pct;

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

  ///////////////////////
  // Randomized fields //
  ///////////////////////

  // OTP variables.
  rand prim_mubi_pkg::mubi8_t   otp_en_es_fw_read, otp_en_es_fw_over;

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
  constraint which_cntr_replicate_c {which_cntr_replicate inside {[0:RNG_BUS_WIDTH-1]};}

  int        num_bins = 2**RNG_BUS_WIDTH;
  rand uint  which_bin;
  constraint which_bin_c {which_bin inside {[0:num_bins-1]};}

  /////////////////
  // Constraints //
  /////////////////

  constraint otp_en_es_fw_read_c {otp_en_es_fw_read dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_read_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_read_pct) };}

  constraint otp_en_es_fw_over_c {otp_en_es_fw_over dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_over_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_over_pct) };}

  constraint spurious_inject_entropy_c {spurious_inject_entropy dist {
      1                         :/ spurious_inject_entropy_pct,
      0                         :/ (100 - spurious_inject_entropy_pct) };}


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

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end

    // get entropy_src assert interface handle
    if (!uvm_config_db#(virtual entropy_src_assert_if)::
        get(null, "*.env" , "entropy_src_assert_vif", entropy_src_assert_vif)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ASSERT IF"))
    end

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str, "\n\t |**************** entropy_src_env_cfg *****************| \t"};

    str = {
        str,
        $sformatf("\n\t |***** otp_en_es_fw_read           : %12s *****| \t",
                  otp_en_es_fw_read.name()),
        $sformatf("\n\t |***** otp_en_es_fw_over           : %12s *****| \t",
                  otp_en_es_fw_over.name()),
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
        $sformatf("\n\t |***** otp_en_es_fw_over_pct       : %12d *****| \t",
                  otp_en_es_fw_over_pct)
    };

    str = {str, "\n\t |******************************************************| \t"};
    str = {str, dut_cfg.convert2string()};

    return str;
  endfunction

  function void post_randomize();
    dut_cfg.randomize();
  endfunction

endclass
