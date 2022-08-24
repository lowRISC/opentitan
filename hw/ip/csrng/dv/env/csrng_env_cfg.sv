// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_env_cfg extends cip_base_env_cfg #(.RAL_T(csrng_reg_block));

  `uvm_object_utils_begin(csrng_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
                                                 m_entropy_src_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(1))   m_aes_halt_agent_cfg;
  rand csrng_agent_cfg                           m_edn_agent_cfg[NUM_HW_APPS];

  virtual pins_if#(MuBi8Width)   otp_en_cs_sw_app_read_vif;
  virtual pins_if#(MuBi4Width)   lc_hw_debug_en_vif;

  virtual csrng_assert_if csrng_assert_vif; // handle to csrng assert interface

  virtual csrng_path_if csrng_path_vif; // handle to csrng path interface

  // Knobs & Weights
  uint   otp_en_cs_sw_app_read_pct, lc_hw_debug_en_pct, regwen_pct,
         enable_pct, sw_app_enable_pct, read_int_state_pct, force_state_pct,
         check_int_state_pct, num_cmds_min, num_cmds_max, aes_halt_pct,
         min_aes_halt_clks, max_aes_halt_clks;

  bit    use_invalid_mubi;

  rand bit       check_int_state, regwen, hw_app[NUM_HW_APPS],
                 sw_app, aes_halt;
  rand mubi4_t   enable, sw_app_enable, read_int_state;
  rand lc_tx_t   lc_hw_debug_en;
  rand mubi8_t   otp_en_cs_sw_app_read;

  rand fatal_err_e      which_fatal_err;
  rand err_code_e       which_err_code;
  rand which_fifo_e     which_fifo;
  rand which_fifo_err_e which_fifo_err;
  rand invalid_mubi_e   which_invalid_mubi;

  bit                                    compliance[NUM_HW_APPS + 1], status[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::KEY_LEN-1:0]       key[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::BLOCK_LEN-1:0]     v[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   reseed_counter[NUM_HW_APPS + 1];

  int                                    NHwApps = 2;
  int                                    NApps = NHwApps + 1;
  int                                    Sp2VWidth = 3;

  rand uint  which_hw_inst_exc;
  constraint which_hw_inst_exc_c { which_hw_inst_exc inside {[0:NHwApps-1]};}

  rand uint  which_sp2v;
  constraint which_sp2v_c { which_sp2v inside {[0:Sp2VWidth-1]};}

  constraint otp_en_cs_sw_app_read_c { otp_en_cs_sw_app_read dist {
                                       MuBi8True  :/ otp_en_cs_sw_app_read_pct,
                                       MuBi8False :/ (100 - otp_en_cs_sw_app_read_pct) };}

  constraint lc_hw_debug_en_c { `DV_LC_TX_DIST(lc_hw_debug_en, lc_hw_debug_en_pct,
                                (100 - lc_hw_debug_en_pct) / 2,  (100 - lc_hw_debug_en_pct) / 2)}

  constraint regwen_c { regwen dist {
                        1 :/ regwen_pct,
                        0 :/ (100 - regwen_pct) };}

  constraint enable_c { enable dist {
                        MuBi4True  :/ enable_pct,
                        MuBi4False :/ (100 - enable_pct) };}

  constraint sw_app_enable_c { sw_app_enable dist {
                               MuBi4True  :/ sw_app_enable_pct,
                               MuBi4False :/ (100 - sw_app_enable_pct) };}

  constraint read_int_state_c { read_int_state dist {
                                MuBi4True  :/ read_int_state_pct,
                                MuBi4False :/ (100 - read_int_state_pct) };}

  constraint check_int_state_c { check_int_state dist {
                                 1 :/ check_int_state_pct,
                                 0 :/ (100 - check_int_state_pct) };}

  constraint aes_halt_c { aes_halt dist {
                          1 :/ aes_halt_pct,
                          0 :/ (100 - aes_halt_pct) };}

  // Functions
  function void post_randomize();
    if (use_invalid_mubi) begin
      prim_mubi_pkg::mubi4_t invalid_mubi_val;
      invalid_mubi_val = get_rand_mubi4_val(.t_weight(0), .f_weight(0), .other_weight(1));

      case (which_invalid_mubi)
        invalid_enable: enable = invalid_mubi_val;
        invalid_sw_app_enable: sw_app_enable = invalid_mubi_val;
        invalid_read_int_state: read_int_state = invalid_mubi_val;
        default: begin
          `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
        end
      endcase // case (which_invalid_mubi)
    end
  endfunction // post_randomize

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = csrng_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create agent configs
    m_entropy_src_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::
                              FIPS_CSRNG_BUS_WIDTH))::type_id::create("m_entropy_src_agent_cfg");

    m_aes_halt_agent_cfg    = push_pull_agent_cfg#(.HostDataWidth(1))::type_id::create
                              ("m_aes_halt_agent_cfg");

    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_agent_cfg[i] = csrng_agent_cfg::type_id::create($sformatf("m_edn_agent_cfg[%0d]", i));
    end

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end

    // get csrng assert interface handle
    if (!uvm_config_db#(virtual csrng_assert_if)::
        get(null, "*.env" , "csrng_assert_vif", csrng_assert_vif)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ASSERT IF"))
    end

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  // Check internal state w/ optional compare
  task check_internal_state(uint app = SW_APP, bit compare = 0);
    bit [TL_DW-1:0]                        rdata;
    bit                                    hw_compliance, hw_status;
    bit [csrng_env_pkg::KEY_LEN-1:0]       hw_key;
    bit [csrng_env_pkg::BLOCK_LEN-1:0]     hw_v;
    bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   hw_reseed_counter;

    csr_wr(.ptr(ral.int_state_num), .value(app));
    // To give the hardware time to update
    clk_rst_vif.wait_clks(1);
    for (int i = 0; i < RSD_CTR_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_reseed_counter = (rdata<<TL_DW*i) + hw_reseed_counter;
    end
    for (int i = 0; i < BLOCK_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_v = (rdata<<TL_DW*i) + hw_v;
    end
    for (int i = 0; i < KEY_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_key = (rdata<<TL_DW*i) + hw_key;
    end
    csr_rd(.ptr(ral.int_state_val), .value(rdata));
    hw_compliance = rdata[1];
    hw_status     = rdata[0];
    `uvm_info(`gfn, $sformatf("\n"), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("************ internal_state[%0d] ***********", app), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("hw_reseed_counter  = %0d", hw_reseed_counter), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.reseed_counter = %0d", reseed_counter[app]), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("hw_v  = 0x%0h", hw_v), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.v = 0x%0h", v[app]), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("hw_key  = 0x%0h", hw_key), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.key = 0x%0h", key[app]), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("hw_compliance/status  = 0b%b", {hw_compliance, hw_status}),
        UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.compliance/status = 0b%b", {compliance[app], status[app]}),
        UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("******************************************\n"), UVM_DEBUG)
    if (compare) begin
      if ((read_int_state == MuBi4True) && (otp_en_cs_sw_app_read == MuBi8True)) begin
        `DV_CHECK_EQ_FATAL(hw_reseed_counter, reseed_counter[app])
        `DV_CHECK_EQ_FATAL(hw_v, v[app])
        `DV_CHECK_EQ_FATAL(hw_key, key[app])
        `DV_CHECK_EQ_FATAL({hw_compliance, hw_status}, {compliance[app], status[app]})
      end
      else begin
        `DV_CHECK_EQ_FATAL(hw_reseed_counter, 0)
        `DV_CHECK_EQ_FATAL(hw_v, 0)
        `DV_CHECK_EQ_FATAL(hw_key, 0)
        `DV_CHECK_EQ_FATAL({hw_compliance, hw_status}, 0)
      end
    end
  endtask

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |**************** csrng_env_cfg *******************| \t")};
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read     : %10s *****| \t",
           otp_en_cs_sw_app_read.name())};
    str = {str,  $sformatf("\n\t |***** lc_hw_debug_en            : %10s *****| \t",
           lc_hw_debug_en.name())};
    str = {str,  $sformatf("\n\t |***** enable                    : %10s *****| \t",
           enable.name())};
    str = {str,  $sformatf("\n\t |***** sw_app_enable             : %10s *****| \t",
           sw_app_enable.name())};
    str = {str,  $sformatf("\n\t |***** read_int_state            : %10s *****| \t",
           read_int_state.name())};
    str = {str,  $sformatf("\n\t |***** regwen                    : %10d *****| \t",
           regwen)};
    str = {str,  $sformatf("\n\t |***** check_int_state           : %10d *****| \t",
           check_int_state)};
    str = {str,  $sformatf("\n\t |---------------- knobs ---------------------------| \t")};
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read_pct : %10d *****| \t",
           otp_en_cs_sw_app_read_pct) };
    str = {str,  $sformatf("\n\t |***** lc_hw_debug_en_pct        : %10d *****| \t",
           lc_hw_debug_en_pct) };
    str = {str,  $sformatf("\n\t |***** enable_pct                : %10d *****| \t",
           enable_pct)};
    str = {str,  $sformatf("\n\t |***** sw_app_enable_pct         : %10d *****| \t",
           sw_app_enable_pct)};
    str = {str,  $sformatf("\n\t |***** read_int_state_pct        : %10d *****| \t",
           read_int_state_pct)};
    str = {str,  $sformatf("\n\t |***** regwen_pct                : %10d *****| \t",
           regwen_pct)};
    str = {str,  $sformatf("\n\t |***** check_int_state_pct       : %10d *****| \t",
           check_int_state_pct)};
    str = {str,  $sformatf("\n\t |***** num_cmds_min              : %10d *****| \t",
           num_cmds_min)};
    str = {str,  $sformatf("\n\t |***** num_cmds_max              : %10d *****| \t",
           num_cmds_max)};
    str = {str,  $sformatf("\n\t |***** min_aes_halt_clks         : %10d *****| \t",
           min_aes_halt_clks)};
    str = {str,  $sformatf("\n\t |***** max_aes_halt_clks         : %10d *****| \t",
           max_aes_halt_clks)};
    str = {str,  $sformatf("\n\t |**************************************************| \t")};
    str = {str, "\n"};
    return str;
  endfunction

endclass
