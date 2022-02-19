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

  // handle to csrng assert interface
  virtual entropy_src_assert_if entropy_src_assert_if;
  // handle to edn path interface
  virtual entropy_src_path_if entropy_src_path_vif;
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

  int      seed_cnt;

  uint     fips_window_size, bypass_window_size, boot_mode_retry_limit;

  bit      use_invalid_mubi;

  /////////////////////
  // Knobs & Weights //
  /////////////////////

  // Constraint knob for module_enable field
  uint          module_enable_pct;

  // Constraint knob for SW-accessible REGWEN-related fields
  uint          me_regwen_pct, sw_regupd_pct;

  // Constraint knobs for Boolean fields in CONF register
  // (RNG_BIT_SEL is always uniform)
  uint          fips_enable_pct, entropy_data_reg_enable_pct, ht_threshold_scope_pct,
                rng_bit_enable_pct;

  // Constraint knobs for Boolean fields in ENTROPY_CONTROL register
  uint          route_software_pct, type_bypass_pct;

  // Constraint knobs for Boolean fields in FW_OV_CONTROL register
  uint          fw_read_pct, fw_over_pct;

  // Knob to inject entropy even if the DUT is configured to not accept it
  rand bit      spurious_inject_entropy_pct;

  // Constraint knobs for OTP-driven inputs
  uint          otp_en_es_fw_read_pct, otp_en_es_fw_over_pct;

  // Behavioral constrint knob: dictates how often each sequence
  // performs a seurvey of the health test diagnostics.
  // (100% corresponds to a full diagnostic chack after every HT alert,
  // If less than 100%, this full-diagnostic is skipped after some alerts)
  uint          do_check_ht_diag_pct;

  // Health test-related knobs
  // Real constraints on sigma ranges (floating point value)
  real adaptp_sigma_max, adaptp_sigma_min;
  real markov_sigma_max, markov_sigma_min;
  real bucket_sigma_max, bucket_sigma_min;

  // Knob to leave thresholds at default, completely disabling them
  uint          default_ht_thresholds_pct;

  ///////////////////////
  // Randomized fields //
  ///////////////////////

  rand bit                      sw_regupd, me_regwen;
  rand bit [1:0]                rng_bit_sel;

  rand prim_mubi_pkg::mubi4_t   module_enable, fips_enable, route_software, type_bypass,
                                entropy_data_reg_enable, rng_bit_enable, ht_threshold_scope;

  rand int                      observe_fifo_thresh;

  rand prim_mubi_pkg::mubi8_t   otp_en_es_fw_read, otp_en_es_fw_over;
  rand prim_mubi_pkg::mubi4_t   fw_read_enable, fw_over_enable;
  rand bit                      spurious_inject_entropy;


  // Note: These integer-valued fields are used to derive their real-valued counterparts.
  rand int unsigned adaptp_sigma_i, markov_sigma_i, bucket_sigma_i;

  // Randomized real values: to be managed in post_randomize
  // Controlled by the knobs <test>_sigma_max, <test>_sigma_min
  real              adaptp_sigma, markov_sigma, bucket_sigma;
  rand int          default_ht_thresholds;

  /////////////////////////////////////////////////////////////////
  // Implementation-specific constants related to the DUT        //
  // (Needed for accurate prediction, no randomization required) //
  /////////////////////////////////////////////////////////////////

  // Number of clock cycles between a TLUL disable signal, and deassertion
  // of enable on the RNG bus.

  int tlul2rng_disable_delay = 1;

  // When expecting an alert, the cip scoreboarding routines expect a to see the
  // alert within alert_max_delay clock cycles.
  int      alert_max_delay;

  // Random values for interrupt, alert and error tests
  rand fatal_err_e      which_fatal_err;
  rand err_code_e       which_err_code;
  rand which_fifo_e     which_fifo;
  rand which_fifo_err_e which_fifo_err;
  rand invalid_mubi_e   which_invalid_mubi;
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

  constraint sw_regupd_c {sw_regupd dist {
      1 :/ sw_regupd_pct,
      0 :/ (100 - sw_regupd_pct) };}

  constraint me_regwen_c {me_regwen dist {
      1 :/ me_regwen_pct,
      0 :/ (100 - me_regwen_pct) };}

  constraint otp_en_es_fw_read_c {otp_en_es_fw_read dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_read_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_read_pct) };}

  constraint otp_en_es_fw_over_c {otp_en_es_fw_over dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_over_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_over_pct) };}

  constraint fw_read_enable_c {fw_read_enable dist {
      prim_mubi_pkg::MuBi4True  :/ fw_read_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - fw_read_pct) };}

  constraint fw_over_enable_c {fw_over_enable dist {
      prim_mubi_pkg::MuBi4True  :/ fw_over_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - fw_over_pct) };}

  constraint spurious_inject_entropy_c {spurious_inject_entropy dist {
      1                         :/ spurious_inject_entropy_pct,
      0                         :/ (100 - spurious_inject_entropy_pct) };}

  constraint module_enable_c {module_enable dist {
      prim_mubi_pkg::MuBi4True  :/ module_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - module_enable_pct) };}

  constraint fips_enable_c {fips_enable dist {
      prim_mubi_pkg::MuBi4True  :/ fips_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - fips_enable_pct) };}

  constraint route_c {route_software dist {
      prim_mubi_pkg::MuBi4True  :/ route_software_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - route_software_pct) };}

  constraint bypass_c {type_bypass dist {
      prim_mubi_pkg::MuBi4True  :/ type_bypass_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - type_bypass_pct) };}

  constraint entropy_data_reg_enable_c {entropy_data_reg_enable dist {
      prim_mubi_pkg::MuBi4True  :/ entropy_data_reg_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - entropy_data_reg_enable_pct) };}

  constraint rng_bit_enable_c {rng_bit_enable dist {
      prim_mubi_pkg::MuBi4True  :/ rng_bit_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - rng_bit_enable_pct) };}

  constraint ht_threshold_scope_c {ht_threshold_scope dist {
      prim_mubi_pkg::MuBi4True  :/ ht_threshold_scope_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - ht_threshold_scope_pct)};}

  constraint default_ht_thresholds_c {default_ht_thresholds dist {
      1 :/ default_ht_thresholds_pct,
      0 :/ (100 - default_ht_thresholds_pct)};}

  // TODO: Is zero a valid value for this register?
  // What does the DUT do with a value of zero?
  constraint observe_fifo_thresh_c {observe_fifo_thresh dist {
      [1:OBSERVE_FIFO_DEPTH]  :/ 1};}

  ///////////////
  // Functions //
  ///////////////

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create agent config objs
    m_rng_agent_cfg   = push_pull_agent_cfg#(.HostDataWidth(RNG_BUS_WIDTH))::
                        type_id::create("m_rng_agent_cfg");
    m_csrng_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))::
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
        get(null, "*.env" , "entropy_src_assert_if", entropy_src_assert_if)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ASSERT IF"))
    end
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
        $sformatf("\n\t |***** module_enable               : %12s *****| \t",
                  module_enable.name()),
        $sformatf("\n\t |***** fips_enable                 : %12s *****| \t",
                  fips_enable.name()),
        $sformatf("\n\t |***** route_software              : %12s *****| \t",
                  route_software.name()),
        $sformatf("\n\t |***** type_bypass                 : %12s *****| \t",
                  type_bypass.name()),
        $sformatf("\n\t |***** entropy_data_reg_enable     : %12s *****| \t",
                  entropy_data_reg_enable.name()),
        $sformatf("\n\t |***** rng_bit_enable              : %12s *****| \t",
                  rng_bit_enable.name()),
        $sformatf("\n\t |***** rng_bit_sel                 : %12d *****| \t",
                  rng_bit_sel),
        $sformatf("\n\t |***** fips_window_size            : %12d *****| \t",
                  fips_window_size),
        $sformatf("\n\t |***** bypass_window_size          : %12d *****| \t",
                  bypass_window_size),
        $sformatf("\n\t |***** boot_mode_retry_limit       : %12d *****| \t",
                  boot_mode_retry_limit),
        $sformatf("\n\t |***** fw_read_enable              : %12s *****| \t",
                  fw_read_enable.name()),
        $sformatf("\n\t |***** fw_over_enable              : %12s *****| \t",
                  fw_over_enable.name()),
        $sformatf("\n\t |***** observe_fifo_threshold      : %12d *****| \t",
                  observe_fifo_thresh),
        $sformatf("\n\t |***** seed_cnt                    : %12d *****| \t",
                  seed_cnt),
        $sformatf("\n\t |***** sim_duration                : %9.2f ms *****| \t",
                  sim_duration/1ms),
        $sformatf("\n\t |***** adaptp_sigma                : %12.3f *****| \t",
                  adaptp_sigma),
        $sformatf("\n\t |***** bucket_sigma                : %12.3f *****| \t",
                  bucket_sigma),
        $sformatf("\n\t |***** markov_sigma                : %12.3f *****| \t",
                  markov_sigma)
    };

    str = {str, "\n\t |----------------- knobs ------------------------------| \t"};

    str = {
        str,
        $sformatf("\n\t |***** otp_en_es_fw_read_pct       : %12d *****| \t",
                  otp_en_es_fw_read_pct),
        $sformatf("\n\t |***** otp_en_es_fw_over_pct       : %12d *****| \t",
                  otp_en_es_fw_over_pct),
        $sformatf("\n\t |***** fw_read_pct                 : %12d *****| \t",
                  fw_read_pct),
        $sformatf("\n\t |***** fw_over_pct                 : %12d *****| \t",
                  fw_over_pct),
        $sformatf("\n\t |***** module_enable_pct           : %12d *****| \t",
                  module_enable_pct),
        $sformatf("\n\t |***** fips_enable_pct             : %12d *****| \t",
                  fips_enable_pct),
        $sformatf("\n\t |***** route_software_pct          : %12d *****| \t",
                  route_software_pct),
        $sformatf("\n\t |***** type_bypass_pct             : %12d *****| \t",
                  type_bypass_pct),
        $sformatf("\n\t |***** entropy_data_reg_enable_pct : %12d *****| \t",
                  entropy_data_reg_enable_pct),
        $sformatf("\n\t |***** rng_bit_enable_pct          : %12d *****| \t",
                  rng_bit_enable_pct),
        $sformatf("\n\t |***** adaptp_sigma range          : (%04.2f, %04.2f) *****| \t",
                  adaptp_sigma_min, adaptp_sigma_max),
        $sformatf("\n\t |***** bucket_sigma range          : (%04.2f, %04.2f) *****| \t",
                  bucket_sigma_min, bucket_sigma_max),
        $sformatf("\n\t |***** markov_sigma range          : (%04.2f, %04.2f) *****| \t",
                  markov_sigma_min, markov_sigma_max)

    };

    str = {str, "\n\t |******************************************************| \t"};
    str = {str, "\n"};
    return str;
  endfunction

  function void post_randomize();
    // temporary variable to map randomized integer variables to the range [0, 1]
    real tmp_r;

    tmp_r = real'(adaptp_sigma_i)/{$bits(adaptp_sigma_i){1'b1}};
    adaptp_sigma = adaptp_sigma_min + (adaptp_sigma_max - adaptp_sigma_min) * tmp_r;

    tmp_r = real'(markov_sigma_i)/{$bits(markov_sigma_i){1'b1}};
    markov_sigma = markov_sigma_min + (markov_sigma_max - markov_sigma_min) * tmp_r;

    tmp_r = real'(bucket_sigma_i)/{$bits(bucket_sigma_i){1'b1}};
    bucket_sigma = bucket_sigma_min + (bucket_sigma_max - bucket_sigma_min) * tmp_r;

    if (use_invalid_mubi) begin
      prim_mubi_pkg::mubi4_t invalid_mubi_val;
      invalid_mubi_val = get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1));

      entropy_src_assert_if.assert_off_alert();

      case (which_invalid_mubi)
        invalid_fips_enable: fips_enable = invalid_mubi_val;
        invalid_entropy_data_reg_enable: entropy_data_reg_enable = invalid_mubi_val;
        invalid_module_enable: module_enable = invalid_mubi_val;
        invalid_threshold_scope: ht_threshold_scope = invalid_mubi_val;
        invalid_rng_bit_enable: rng_bit_enable = invalid_mubi_val;
        invalid_fw_ov_mode: fw_read_enable = invalid_mubi_val;
        invalid_fw_ov_entropy_insert: fw_over_enable = invalid_mubi_val;
        invalid_es_route: route_software = invalid_mubi_val;
        invalid_es_type: type_bypass = invalid_mubi_val;
        default: begin
          `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
        end
      endcase // case (which_invalid_mubi)
    end
  endfunction

endclass
