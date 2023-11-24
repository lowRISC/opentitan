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

  virtual csrng_agents_if csrng_agents_vif;

  // Knobs & Weights
  uint otp_en_cs_sw_app_read_pct, otp_en_cs_sw_app_read_inval_pct, lc_hw_debug_en_pct, regwen_pct,
       enable_pct, sw_app_enable_pct, read_int_state_pct, force_state_pct, check_int_state_pct,
       num_cmds_min, num_cmds_max, aes_halt_pct, min_aes_halt_clks, max_aes_halt_clks,
       min_num_disable_enable, max_num_disable_enable,
       min_enable_clks, max_enable_clks,
       min_disable_edn_before_csrng_clks, max_disable_edn_before_csrng_clks,
       min_disable_csrng_before_entropy_src_clks, max_disable_csrng_before_entropy_src_clks,
       min_disable_clks, max_disable_clks,
       min_enable_entropy_src_before_csrng_clks, max_enable_entropy_src_before_csrng_clks,
       min_enable_csrng_before_edn_clks, max_enable_csrng_before_edn_clks;

  bit    use_invalid_mubi;

  rand bit       check_int_state, regwen, hw_app[NUM_HW_APPS],
                 sw_app, aes_halt;
  rand mubi4_t   enable, sw_app_enable, read_int_state;
  rand bit [3:0] lc_hw_debug_en;
  rand bit [7:0] otp_en_cs_sw_app_read;

  rand fatal_err_e      which_fatal_err;
  rand err_code_e       which_err_code;
  rand which_fifo_e     which_fifo;
  rand which_fifo_err_e which_fifo_err;
  rand invalid_mubi_e   which_invalid_mubi;
  rand which_cnt_e      which_cnt;
  rand which_aes_cm_e   which_aes_cm;

  bit                                    compliance[NUM_HW_APPS + 1], status[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::KEY_LEN-1:0]       key[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::BLOCK_LEN-1:0]     v[NUM_HW_APPS + 1];
  bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   reseed_counter[NUM_HW_APPS + 1];

  int NHwApps = NUM_HW_APPS;
  int NApps = NHwApps + 1;
  int Sp2VWidth = 3;

  rand uint  which_app_err_alert;
  constraint which_app_err_alert_c { which_app_err_alert inside {[0:NApps-1]};}

  rand uint  which_hw_inst_exc;
  constraint which_hw_inst_exc_c { which_hw_inst_exc inside {[0:NHwApps-1]};}

  rand uint  which_sp2v;
  constraint which_sp2v_c { which_sp2v inside {[0:Sp2VWidth-1]};}

  constraint otp_en_cs_sw_app_read_c {
    `DV_MUBI8_DIST(otp_en_cs_sw_app_read,
                   otp_en_cs_sw_app_read_pct,
                   100 - otp_en_cs_sw_app_read_pct - otp_en_cs_sw_app_read_inval_pct,
                   otp_en_cs_sw_app_read_inval_pct)
  }

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

  // Behind the aes_cipher_sm_err error code, there are which_aes_cm.num() countermeasures each of
  // which can be stimulated by forcing the Sp2VWidth independent logic rails. We bias error
  // distributions towards aes_cipher_sm_err to get away with a reasonable number of seeds.
  int num_bins_aes_cipher_sm_err = which_aes_cm.num() * Sp2VWidth;
  constraint which_fatal_err_c { which_fatal_err dist {
      [sfifo_cmd_error : sfifo_blkenc_error]     := 3, // 3 error types per sfifo
      [cmd_stage_sm_error : drbg_updob_sm_error] := 1, // 1 error type per FSM
      aes_cipher_sm_error                        := num_bins_aes_cipher_sm_err,
      cmd_gen_cnt_error                          := 3, // 3 counters feed into this bit
      [fifo_write_error : fifo_state_error]      := 1
  };}
  constraint which_err_code_c { which_err_code dist {
      [sfifo_cmd_err : sfifo_blkenc_err]     := 3, // 3 error types per sfifo
      [cmd_stage_sm_err : drbg_updob_sm_err] := 1, // 1 error type per FSM
      aes_cipher_sm_err                      := num_bins_aes_cipher_sm_err,
      cmd_gen_cnt_err                        := 3, // 3 counters feed into this bit
      [fifo_write_err : fifo_state_err_test] := 1
  };}

  // Number of times CSRNG gets disabled and re-enabled
  rand uint num_disable_enable;
  constraint num_disable_enable_c {
    num_disable_enable >= min_num_disable_enable;
    num_disable_enable <= max_num_disable_enable;
  }

  // In tests that disable CSRNG, how many cycles to keep all agents and CSRNG enabled
  rand uint enable_clks;
  constraint edn_enable_clks_c {
    enable_clks >= min_enable_clks;
    enable_clks <= max_enable_clks;
  }

  // In tests that disable CSRNG, how many cycles to wait to disable CSRNG after EDN agents have
  // been disabled
  rand uint disable_edn_before_csrng_clks;
  constraint disable_edn_before_csrng_clks_c {
    disable_edn_before_csrng_clks >= min_disable_edn_before_csrng_clks;
    disable_edn_before_csrng_clks <= max_disable_edn_before_csrng_clks;
  }

  // In tests that disable CSRNG, how many cycles to wait to disable entropy_src after CSRNG has
  // been disabled
  rand uint disable_csrng_before_entropy_src_clks;
  constraint disable_csrng_before_entropy_src_clks_c {
    disable_csrng_before_entropy_src_clks >= min_disable_csrng_before_entropy_src_clks;
    disable_csrng_before_entropy_src_clks <= max_disable_csrng_before_entropy_src_clks;
  }

  // In tests that disable CSRNG, how many cycles to keep all agents and CSRNG disabled
  rand uint disable_clks;
  constraint disable_clks_c {
    disable_clks >= min_disable_clks;
    disable_clks <= max_disable_clks;
  }

  // In tests that disable CSRNG, how many cycles to enable the entropy_src agent in advance of
  // CSRNG
  rand uint enable_entropy_src_before_csrng_clks;
  constraint enable_entropy_src_before_csrng_clks_c {
    enable_entropy_src_before_csrng_clks >= min_enable_entropy_src_before_csrng_clks;
    enable_entropy_src_before_csrng_clks <= max_enable_entropy_src_before_csrng_clks;
  }

  // In tests that disable CSRNG, how many cycles to enable CSRNG in advance of enabling EDN agents
  rand uint enable_csrng_before_edn_clks;
  constraint enable_csrng_before_edn_clks_c {
    enable_csrng_before_edn_clks >= min_enable_csrng_before_edn_clks;
    enable_csrng_before_edn_clks <= max_enable_csrng_before_edn_clks;
  }

  // Re-randomize enable and disable delays.  This is intended to be called between iterations in
  // tests that disable and re-enable CSRNG (and the agents).
  function automatic void randomize_disable_enable_clks();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(enable_clks)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(disable_edn_before_csrng_clks)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(disable_csrng_before_entropy_src_clks)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(disable_clks)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(enable_entropy_src_before_csrng_clks)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(enable_csrng_before_edn_clks)
  endfunction

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
    num_interrupts = ral.intr_state.get_n_used_bits();

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
    bit [TL_DW-1:0]                      rdata;
    bit                                  hw_compliance, hw_status;
    bit [csrng_env_pkg::KEY_LEN-1:0]     hw_key;
    bit [csrng_env_pkg::BLOCK_LEN-1:0]   hw_v;
    bit [csrng_env_pkg::RSD_CTR_LEN-1:0] hw_reseed_counter;

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
    str = {str,  $sformatf("\n\t |**************** csrng_env_cfg *************************| \t")};
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read           :       'h%02h *****| \t",
           otp_en_cs_sw_app_read)};
    str = {str,  $sformatf("\n\t |***** lc_hw_debug_en                  :       'h%02h *****| \t",
           lc_hw_debug_en)};
    str = {str,  $sformatf("\n\t |***** enable                          : %10s *****| \t",
           enable.name())};
    str = {str,  $sformatf("\n\t |***** sw_app_enable                   : %10s *****| \t",
           sw_app_enable.name())};
    str = {str,  $sformatf("\n\t |***** read_int_state                  : %10s *****| \t",
           read_int_state.name())};
    str = {str,  $sformatf("\n\t |***** regwen                          : %10d *****| \t",
           regwen)};
    str = {str,  $sformatf("\n\t |***** check_int_state                 : %10d *****| \t",
           check_int_state)};
    str = {str,  $sformatf("\n\t |---------------- knobs ---------------------------------| \t")};
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read_pct       : %10d *****| \t",
           otp_en_cs_sw_app_read_pct) };
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read_inval_pct : %10d *****| \t",
           otp_en_cs_sw_app_read_pct) };
    str = {str,  $sformatf("\n\t |***** lc_hw_debug_en_pct              : %10d *****| \t",
           lc_hw_debug_en_pct) };
    str = {str,  $sformatf("\n\t |***** enable_pct                      : %10d *****| \t",
           enable_pct)};
    str = {str,  $sformatf("\n\t |***** sw_app_enable_pct               : %10d *****| \t",
           sw_app_enable_pct)};
    str = {str,  $sformatf("\n\t |***** read_int_state_pct              : %10d *****| \t",
           read_int_state_pct)};
    str = {str,  $sformatf("\n\t |***** regwen_pct                      : %10d *****| \t",
           regwen_pct)};
    str = {str,  $sformatf("\n\t |***** check_int_state_pct             : %10d *****| \t",
           check_int_state_pct)};
    str = {str,  $sformatf("\n\t |***** num_cmds_min                    : %10d *****| \t",
           num_cmds_min)};
    str = {str,  $sformatf("\n\t |***** num_cmds_max                    : %10d *****| \t",
           num_cmds_max)};
    str = {str,  $sformatf("\n\t |***** min_aes_halt_clks               : %10d *****| \t",
           min_aes_halt_clks)};
    str = {str,  $sformatf("\n\t |***** max_aes_halt_clks               : %10d *****| \t",
           max_aes_halt_clks)};
    str = {str,  $sformatf("\n\t |********************************************************| \t")};
    str = {str, "\n"};
    return str;
  endfunction

endclass
