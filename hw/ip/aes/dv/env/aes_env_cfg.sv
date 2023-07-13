// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env_cfg extends cip_base_env_cfg #(.RAL_T(aes_reg_block));

  `uvm_object_utils_begin(aes_env_cfg)
  `uvm_object_utils_end
  `uvm_object_new

  virtual pins_if #($bits(lc_ctrl_pkg::lc_tx_t) + 1) lc_escalate_vif;
  virtual pins_if #(1) idle_vif;
  virtual aes_reseed_if aes_reseed_vif;
  virtual aes_masking_reseed_if aes_masking_reseed_vif;
  virtual force_if#(.Signal("aes_ctrl_cs"),
                    .SignalWidth(aes_env_pkg::StateWidth)
                   ) aes_fi_vif[Sp2VWidth];
  virtual force_if#(.Signal("aes_cipher_ctrl_cs"),
                    .SignalWidth(aes_env_pkg::StateWidth)
                   ) aes_cipher_fi_vif[Sp2VWidth];
  virtual force_if#(.Signal("aes_ctr_cs"),
                    .SignalWidth(aes_env_pkg::StateWidth)
                   ) aes_ctr_fi_vif[Sp2VWidth];

  virtual fi_control_if aes_control_fi_vif[Sp2VWidth];
  virtual fi_cipher_if aes_cipher_control_fi_vif[Sp2VWidth];
  virtual fi_ctr_fsm_if aes_ctr_fsm_fi_vif[Sp2VWidth];
  virtual fi_core_if aes_core_fi_vif;

  rand key_sideload_agent_cfg keymgr_sideload_agent_cfg;
  // test environment constraints //
  typedef enum { VerySlow, Slow, Fast, VeryFast } tl_ul_access_e;
  //  Message Knobs //
  int                num_messages_min            = 1;
  int                num_messages_max            = 1;
  int                message_len_min             = 128;
  int                message_len_max             = 128;
  bit                use_key_mask                = 0;
  bit                use_c_model_pct             = 0;

  // clear registers with 0's or rand
  bit                clear_reg_w_rand            = 1;
  // if set the order of which key iv and data is written will be randomized and interleaved
  bit                random_data_key_iv_order    = 1;

  // Mode distribution //
  // There are 5 modes (ecb, cbc, ofb, cfb, ctr). The weight for mode X is called X_weight. By
  // default, all weights are set equal at 10 (so each is selected 10/50 = 20% of the time).
  int                ecb_weight                 = 10;
  int                cbc_weight                 = 10;
  int                ofb_weight                 = 10;
  int                cfb_weight                 = 10;
  int                ctr_weight                 = 10;

  // KEYLEN weights
  // change of selecting 128b key
  //  128b/(128+192+256) = 10/30 = (33%)
  int                key_128b_weight            = 10;
  int                key_192b_weight            = 10;
  int                key_256b_weight            = 10;

  // reseed weigth
  int                per8_weight                = 60;
  int                per64_weight               = 30;
  int                per8k_weight               = 10;

  // use manual operation mode percentage
  int                manual_operation_pct       = 10;
  // enable reseed on key touch
  int                reseed_en                  = 1;

  // debug / directed test knobs
  // use fixed key
  bit                fixed_key_en               = 0;
  // use fixed data (same data for each block in a message)
  bit                fixed_data_en              = 0;
  // fixed operation
  bit                fixed_operation_en         = 0;
  bit                fixed_operation            = 1'b0;
  // fixed iv (will set all to bits 0)
  bit                fixed_iv_en                = 0;

  bit                fixed_keylen_en            = 0;
  bit [2:0]          fixed_keylen               = 3'b001;


  //   [0]: configuration errors
  //   [1]: malicous injection
  //   [2]: random resets
  //   [3]: inject Lc_escalate
  error_types_t      error_types                = 4'b1111;

  //   [2]: reseed error
  //   [1]: mode error
  //   [0]: key_len
  cfg_error_type_t   config_error_type          = 3'b111;
  int                config_error_pct           = 30;

  // min and max wait (clk) before an error injection
  // this is only for injection and random reset
  int                inj_min_delay              = 10;
  int                inj_max_delay              = 1000;
  rand int           inj_delay;

  rand alert_reset_trigger_e alert_reset_trigger;

  // clear register percentage
  // percentage of items that will try to clear
  // one or more registers
  int                clear_reg_pct              = 0;

  // should the read vs write be unbalanced.
  bit                unbalanced = 0;
  // chance of reading valid output (for each status poll)
  int                read_prob = 80;
  // chance of writing data when DUT is ready (for each status poll)
  int                write_prob = 90;

  // sideload enable
  int                sideload_pct               = 0;

  ///////////////////////////////
  // dont touch updated by env //
  ///////////////////////////////

  // keep track of:
  // - total number of expected messages
  int                num_messages_tot           = 0;
  // - number of messages that was selected to be corrupt
  //   these should be excluded from the num_messages count
  //   when checking that all messages was processed
  int                num_corrupt_messages       = 0;
  // - number of good messages
  int                good_cnt                   = 0;
  // - number of aes_mode errors seen
  int                corrupt_cnt                = 0;
  // - number of skipped messages
  int                skipped_cnt                = 0;
  // - number of packets that were split
  int                split_cnt                  = 0;

  // rand variables
  // 0: C model 1: OPEN_SSL/BORING_SSL
  rand bit           ref_model;
  // randomly select if we force unused key bits to 0
  rand bit           key_mask;
  // number of messages to encrypt/decrypt
  rand int           num_messages;

  // TL UL contraints //
  rand tl_ul_access_e host_resp_speed;

  rand bit           do_reseed;

  rand bit [2:0]     reseed_rate;

  // constraints
  constraint do_reseed_c    { if (reseed_en == 0) { do_reseed == 0};}
  constraint num_messages_c {num_messages inside {[num_messages_min : num_messages_max]};}
  constraint ref_model_c    {ref_model    dist   { 0 :/ use_c_model_pct,
                                                   1 :/ (100 - use_c_model_pct)};}

  constraint inj_delay_c    {inj_delay    inside {[inj_min_delay : inj_max_delay]};}

  constraint alert_reset_trigger_c {
      if ( |error_types[3:1]) {
          alert_reset_trigger dist { ShadowRegStorageErr :/ 4 * error_types.mal_inject,
                                     PullReset           :/ 4 * error_types.reset,
                                     LcEscalate          :/ 4 * error_types.lc_esc,
                                     AlertTest           :/     error_types.mal_inject};
        } else {
          alert_reset_trigger == ShadowRegStorageErr;
        }
      }

  constraint reseed_rate_c {reseed_rate dist { 3'b001 :/ 1,
                                               3'b010 :/ 1,
                                               3'b100 :/ 1 };}

  function void post_randomize();
    `uvm_info(`gfn, $sformatf("Use KEY MAST: %b", use_key_mask), UVM_LOW)
    if (use_key_mask) key_mask = 1;

    case(host_resp_speed)
      VerySlow: begin
        m_tl_agent_cfg.d_ready_delay_min = 10;
        m_tl_agent_cfg.d_ready_delay_max = 10;
      end
      Slow: begin
        m_tl_agent_cfg.d_ready_delay_min = 4;
        m_tl_agent_cfg.d_ready_delay_max = 10;
      end
      Fast: begin
        m_tl_agent_cfg.d_ready_delay_min = 0;
        m_tl_agent_cfg.d_ready_delay_max = 5;
      end
      VeryFast: begin
        m_tl_agent_cfg.d_ready_delay_min = 0;
        m_tl_agent_cfg.d_ready_delay_max = 0;
        zero_delays                      = 1;
      end
    endcase
  endfunction


  virtual function string convert2string();
    string str = "";
    str = super.convert2string();
    str = {str,  $sformatf("\n\t ----| AES ENVIRONMENT CONFIG \t ") };
    str = {str,  $sformatf("\n\t ----| Max Number of message %d \t ", num_messages_max)};
    str = {str,  $sformatf("\n\t ----| Min Number of message %d \t ", num_messages_min)};
    str = {str,  $sformatf("\n\t ----| Max message len %d bytes \t ", message_len_max)};
    str = {str,  $sformatf("\n\t ----| Min message len %d bytes \t ", message_len_min)};
    str = {str,  $sformatf("\n\t ----| Host response speed %s   \t ", host_resp_speed.name())};
    str = {str,  $sformatf("\n\t ----| Reference model:\t    %s              \t ",
         (ref_model==0) ? "C-MODEL" : "OPEN_SSL" )};
    str = {str,  $sformatf("\n\t ----| num_messages # %d \t ", num_messages)};
    str = {str,  $sformatf("\n\t ----| ECB Weight: %d         \t ", ecb_weight)};
    str = {str,  $sformatf("\n\t ----| CBC Weight: %d         \t ", cbc_weight)};
    str = {str,  $sformatf("\n\t ----| CFB Weight: %d         \t ", cfb_weight)};
    str = {str,  $sformatf("\n\t ----| OFB Weight: %d         \t ", ofb_weight)};
    str = {str,  $sformatf("\n\t ----| CTR Weight: %d         \t ", ctr_weight)};
    str = {str,  $sformatf("\n\t ----| key mask:   %b         \t ", key_mask)};
    str = {str,  $sformatf("\n\t ----| inj delay:  %d         \t ", inj_delay)};
    str = {str, "\n"};
    return str;
  endfunction

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = aes_env_pkg::LIST_OF_ALERTS;
    keymgr_sideload_agent_cfg = key_sideload_agent_cfg#(keymgr_pkg::hw_key_req_t)::type_id
                                ::create("keymgr_sideload_agent_cfg");
    keymgr_sideload_agent_cfg.start_default_seq = 0;
    num_edn = 1;
    super.initialize(csr_base_addr);
    tl_intg_alert_fields[ral.status.alert_fatal_fault] = 1;
    shadow_update_err_status_fields[ral.status.alert_recov_ctrl_update_err] = 1;
    shadow_storage_err_status_fields[ral.status.alert_fatal_fault] = 1;
    // get aes reseed check interface handle
    if (!uvm_config_db#(virtual aes_reseed_if)::get(null, "*.env" , "aes_reseed_vif",
                                                    aes_reseed_vif)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO AES RESEED IF"))
    end
    if (`EN_MASKING) begin
      if (!uvm_config_db#(virtual aes_masking_reseed_if)::get(null, "*.env" ,
          "aes_masking_reseed_vif", aes_masking_reseed_vif)) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO AES MASKING RESEED IF"))
      end
    end
    foreach (aes_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual force_if#(.Signal("aes_ctrl_cs"),
                                            .SignalWidth(aes_env_pkg::StateWidth))
                                           )::get(null, "*.env", $sformatf("aes_fi_vif_%0d", nn),
                                                  aes_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO FALT INJECT INTERFACE %d",nn))
      end
    end
    foreach (aes_cipher_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual force_if#(.Signal("aes_cipher_ctrl_cs"),
                                            .SignalWidth(aes_env_pkg::StateWidth))
                                           )::get(null, "*.env",
                           $sformatf("aes_cipher_fi_vif_%0d",  nn), aes_cipher_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO CIPHER FALT INJECT INTERFACE %d",nn))
      end
    end
    foreach (aes_ctr_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual force_if#(.Signal("aes_ctr_cs"),
                                            .SignalWidth(aes_env_pkg::StateWidth))
                                           )::get(null, "*.env",
                           $sformatf("aes_ctr_fi_vif_%0d",  nn), aes_ctr_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ROUND COUNTER INJECT INTERFACE %d",nn))
      end
    end

    foreach (aes_control_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual fi_control_if)::get(null, "*.env",
                           $sformatf("aes_control_fi_vif_%0d",  nn), aes_control_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ROUND COUNTER INJECT INTERFACE %d",nn))
      end
    end
    foreach (aes_cipher_control_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual fi_cipher_if)::get(null, "*.env",
                           $sformatf("aes_cipher_control_fi_vif_%0d",  nn),
                           aes_cipher_control_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ROUND COUNTER INJECT INTERFACE %d",nn))
      end
    end
    foreach (aes_ctr_fsm_fi_vif[nn]) begin
      if (!uvm_config_db#(virtual fi_ctr_fsm_if)::get(null, "*.env",
                           $sformatf("aes_ctr_fsm_fi_vif_%0d",  nn),
                           aes_ctr_fsm_fi_vif[nn])) begin
        `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO ROUND COUNTER INJECT INTERFACE %d",nn))
      end
    end
    if (!uvm_config_db#(virtual fi_core_if)::get(null, "*.env", "aes_core_fi_vif",
                         aes_core_fi_vif)) begin
      `uvm_fatal(`gfn, "FAILED TO GET HANDLE TO CORE FAULT INJECTION INTERFACE")
    end

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction
endclass
