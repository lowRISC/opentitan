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

  /////////////////////
  // Knobs & Weights //
  /////////////////////

  uint          enable_pct, route_software_pct, regwen_pct, fw_read_pct, fw_over_pct,
                otp_en_es_fw_read_pct, otp_en_es_fw_over_pct, entropy_data_reg_enable_pct,
                rng_bit_enable_pct, do_check_ht_diag_pct, type_bypass_pct, boot_bypass_disable_pct;



  // Health test knobs:
  real adaptp_sigma_max, adaptp_sigma_min;
  real markov_sigma_max, markov_sigma_min;
  real bucket_sigma_max, bucket_sigma_min;

  ///////////////////////
  // Randomized fields //
  ///////////////////////

  rand bit         regwen;
  rand bit [1:0]   rng_bit_sel;

  rand prim_mubi_pkg::mubi4_t   enable, route_software, type_bypass,
                                boot_bypass_disable, entropy_data_reg_enable,
                                rng_bit_enable;


  rand int                      observe_fifo_thresh;

  rand prim_mubi_pkg::mubi8_t   otp_en_es_fw_read, otp_en_es_fw_over;
  rand prim_mubi_pkg::mubi4_t   fw_read_enable, fw_over_enable;


  // Note: These integer-valued fields are used to derive their real-valued counterparts.
  rand int unsigned adaptp_sigma_i, markov_sigma_i, bucket_sigma_i;

  // Randomized real values: to be managed in post_randomize
  // Controlled by the knobs <test>_sigma_max, <test>_sigma_min
  real              adaptp_sigma, markov_sigma, bucket_sigma;

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

  /////////////////
  // Constraints //
  /////////////////

  constraint regwen_c {regwen dist {
      1 :/ regwen_pct,
      0 :/ (100 - regwen_pct) };}

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

  constraint enable_c {enable dist {
      prim_mubi_pkg::MuBi4True  :/ enable_pct,
      prim_mubi_pkg::MuBi4False :/ 100 - enable_pct };}

  constraint route_c {route_software dist {
      prim_mubi_pkg::MuBi4True  :/ route_software_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - route_software_pct) };}

  constraint bypass_c {type_bypass dist {
      prim_mubi_pkg::MuBi4True  :/ type_bypass_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - type_bypass_pct) };}

  constraint boot_bypass_disable_c {boot_bypass_disable dist {
      prim_mubi_pkg::MuBi4True  :/ boot_bypass_disable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - boot_bypass_disable_pct)};}

  constraint entropy_data_reg_enable_c {entropy_data_reg_enable dist {
      prim_mubi_pkg::MuBi4True  :/ entropy_data_reg_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - entropy_data_reg_enable_pct)};}

  constraint rng_bit_enable_c {rng_bit_enable dist {
      prim_mubi_pkg::MuBi4True  :/ rng_bit_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - rng_bit_enable_pct)};}

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
        $sformatf("\n\t |***** enable                      : %12s *****| \t",
                 enable.name()),
        $sformatf("\n\t |***** route_software              : %12s *****| \t",
                  route_software.name()),
        $sformatf("\n\t |***** type_bypass                 : %12s *****| \t",
                   type_bypass.name()),
        $sformatf("\n\t |***** entropy_data_reg_enable     : %12s *****| \t",
                  entropy_data_reg_enable.name()),
        $sformatf("\n\t |***** boot_bypass_disable         : %12s *****| \t",
                  boot_bypass_disable.name()),
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
        $sformatf("\n\t |***** enable_pct                  : %12d *****| \t",
                  enable_pct),
        $sformatf("\n\t |***** route_software_pct          : %12d *****| \t",
                  route_software_pct),
        $sformatf("\n\t |***** type_bypass_pct             : %12d *****| \t",
                  type_bypass_pct),
        $sformatf("\n\t |***** entropy_data_reg_enable_pct : %12d *****| \t",
                  entropy_data_reg_enable_pct),
        $sformatf("\n\t |***** boot_bypass_disable_pct     : %12d *****| \t",
                  boot_bypass_disable_pct),
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

  endfunction

endclass
