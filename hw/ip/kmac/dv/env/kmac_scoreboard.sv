// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define KMAC_APP_VALID_TRANS(mode) \
    (cfg.m_kmac_app_agent_cfg[``mode``].vif.req_data_if.valid && \
     cfg.m_kmac_app_agent_cfg[``mode``].vif.req_data_if.ready)

`define CALC_PARTIAL_MSG \
    (!in_kmac_app && msg.size() % 8 > 0) || \
      (in_kmac_app && \
        (app_mode == AppKeymgr && (kmac_app_msg.size() + 3) % 8 > 0) || \
        (app_mode != AppKeymgr && kmac_app_msg.size() % 8 > 0))

class kmac_scoreboard extends cip_base_scoreboard #(
    .CFG_T(kmac_env_cfg),
    .RAL_T(kmac_reg_block),
    .COV_T(kmac_env_cov)
  );
  `uvm_component_utils(kmac_scoreboard)

  // local variables

  bit do_check_digest = 1;

  // used solely for coverage sampling, indicates that keccak rounds are currently running
  bit in_keccak_rounds = 0;

  // Whenever the keccak rounds are running, the `complete` signal is raised at the end
  // for a single cycle to signal to sha3 control logic that the keccak engine is completed.
  //
  // There are some edge cases that may occur if a CmdProcess or a `kmac_app_last`is seen on this
  // "complete" cycle that need to be handled - this bit will be raised and lowered in conjunction
  // with the internal `complete` signal to allow the scb easier handling of these scenarios.
  bit keccak_complete_cycle = 0;

  // this bit tracks the beginning and end of a KMAC_APP operation
  bit in_kmac_app;

  // Indicates what application is using the app interface
  kmac_app_e app_mode;

  // this bit goes high for a cycle when a manual squeezing is requested
  bit req_manual_squeeze = 0;

  // The CFG.entropy_ready field is only used to transition the entropy FSM into fetching entropy
  // from the reset state, so we can only rely on writes to CFG.entropy_ready to update internal
  // scoreboard state after a reset is seen.
  //
  // To that effect, we set this bit to 1 any time the scoreboard is reset, and will unset it
  // the first time that CFG.entropy_ready is updated.
  bit first_op_after_rst = 0;

  // CFG fields
  bit kmac_en;
  bit sideload_en;
  sha3_pkg::sha3_mode_e hash_mode;
  sha3_pkg::keccak_strength_e strength;
  entropy_mode_e entropy_mode = EntropyModeNone;
  bit entropy_fast_process;
  bit entropy_ready;

  // Set this bit when entropy_ready is 1 and entropy_mode is EntropyModeEdn,
  // to indicate that we are now waiting on the EDN to return valid entropy
  bit in_edn_fetch = 0;

  // CMD fields
  kmac_cmd_e unchecked_kmac_cmd = CmdNone;
  kmac_cmd_e checked_kmac_cmd = CmdNone;

  bit msg_digest_done;

  // SHA3 status bits
  bit sha3_idle;
  bit sha3_absorb;
  bit sha3_squeeze;

  bit intr_kmac_done;
  bit intr_fifo_empty;
  bit intr_kmac_err;

  // Error tracking
  kmac_pkg::err_t kmac_err = '{valid: 1'b0,
                               code: kmac_pkg::ErrNone,
                               info: '0};
  sha3_pkg::err_t sha3_err = '{valid: 1'b0,
                               code: sha3_pkg::ErrNone,
                               info: '0};
  // Need to track the FSM in `kmac_app` and the mux select value,
  // these are used in App-related error reporting
  kmac_app_st_e   app_st = StIdle;
  bit             app_fsm_active = 0;
  app_mux_sel_e   app_mux_sel = SelNone;

  // key length enum
  key_len_e key_len;

  bit [keymgr_pkg::KmacDataIfWidth-1:0]   kmac_app_block_data;
  bit [keymgr_pkg::KmacDataIfWidth/8-1:0] kmac_app_block_strb;
  int kmac_app_block_strb_size = 0;
  bit kmac_app_last;

  // secret keys
  //
  // max key size is 512-bits
  bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] keys;

  // prefix words
  bit [31:0] prefix[KMAC_NUM_PREFIX_WORDS];

  // input message
  bit [7:0] msg[$];

  // input message from keymgr
  byte kmac_app_msg[$];

  // output digest from KMAC_APP intf (256 bits each)
  bit [kmac_pkg::AppDigestW-1:0] kmac_app_digest_share0;
  bit [kmac_pkg::AppDigestW-1:0] kmac_app_digest_share1;

  // output digests
  bit [7:0] digest_share0[];
  bit [7:0] digest_share1[];

  // This mask is used to mask reads from the state windows.
  // We need to make this a class variable as we set the mask value
  // during the address read phase, but then need its value to persist
  // through the data read phase.
  bit [TL_DBW-1:0] state_mask;

  // This mask is used to avoid building a cycle accurate scoreboard to check kmac message fifo.
  // This SCB will only check that when KmacStatusFifoFull is set, the FIFO depth should be full
  // depth; when KmacStatusFifoEmpty is set, the FIFO depth should be 0. If none of them are set,
  // the Fifo depth should be between 0 and the max value.
  // The actually FIFO depth is covered in direct sequence.
  bit [TL_DW-1:0] status_mask = (1'b1 << KmacStatusFifoFull) |
                                (1'b1 << KmacStatusFifoEmpty) |
                                ({KMAC_FIFO_DEPTH{1'b1}} << KmacStatusFifoDepthLSB);

  // TLM fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_app_rsp_fifo[kmac_pkg::NumAppIntf];
  uvm_tlm_analysis_fifo #(push_pull_agent_pkg::push_pull_item #(
    .HostDataWidth(kmac_app_agent_pkg::KMAC_REQ_DATA_WIDTH)))
    kmac_app_req_fifo[kmac_pkg::NumAppIntf];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int i = 0; i < kmac_pkg::NumAppIntf; i++) begin
      kmac_app_req_fifo[i] = new($sformatf("kmac_app_req_fifo[%0d]", i), this);
      kmac_app_rsp_fifo[i] = new($sformatf("kmac_app_rsp_fifo[%0d]", i), this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        process_checked_kmac_cmd();
        detect_kmac_app_start();
        process_kmac_app_fsm();
        process_edn();
        process_kmac_app_req_fifo();
        process_kmac_app_rsp_fifo();
        process_sideload_key();
      join_none
    end
  endtask

  // This task spins forever and assigns `checked_kmac_cmd` to `unchecked_kmac_cmd`
  // with a 1 cycle delay.
  virtual task process_checked_kmac_cmd();
    @(negedge cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          @(unchecked_kmac_cmd);
          `uvm_info(`gfn, "BEFORE LATCHING KMAC_CMD", UVM_HIGH)
          `uvm_info(`gfn, $sformatf("unchecked_kmac_cmd: %0s", unchecked_kmac_cmd.name()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("checked_kmac_cmd: %0s", checked_kmac_cmd.name()), UVM_HIGH)
          cfg.clk_rst_vif.wait_clks(1);
          checked_kmac_cmd = unchecked_kmac_cmd;
          `uvm_info(`gfn, "AFTER LATCHING KMAC_CMD", UVM_HIGH)
          `uvm_info(`gfn, $sformatf("unchecked_kmac_cmd: %0s", unchecked_kmac_cmd.name()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("checked_kmac_cmd: %0s", checked_kmac_cmd.name()), UVM_HIGH)

          if (checked_kmac_cmd == CmdStart) begin
            sha3_idle = 0;
            sha3_absorb = 1;
            `uvm_info(`gfn, "raised sha3_absorb and dropped sha3_idle when issued start cmd",
                      UVM_HIGH)
          end
          if (checked_kmac_cmd == CmdDone) sha3_idle = 1;
          // If CmdDone is written, we know that a hash has completed.
          // So, we can set this to CmdNone one cycle later.
          cfg.clk_rst_vif.wait_clks(1);
          if (checked_kmac_cmd == CmdDone) begin
            checked_kmac_cmd = CmdNone;
          end
          ,
          wait(cfg.under_reset);
      )
    end
  endtask

  // This task waits until an entropy request is sent,
  // then waits for valid entropy to be returned from EDN
  virtual task process_edn();
    push_pull_agent_pkg::push_pull_item #(.DeviceDataWidth(cip_base_pkg::EDN_DATA_WIDTH)) edn_item;
    @(negedge cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          forever begin
            @(posedge in_edn_fetch);
            // Entropy interface is native 32 bits - prim_edn_req component internally
            // does as many EDN fetches as necessary to fill up the required data bus size
            // of the "host".
            repeat (kmac_reg_pkg::NumSeedsEntropyLfsr) begin
              `DV_SPINWAIT(edn_fifos[0].get(edn_item);, "Wait EDN request")
            end
            `uvm_info(`gfn, "got all edn transactions", UVM_HIGH)
            set_entropy_fetch(0);
          end
          ,
          wait(cfg.under_reset);
      )
    end
  endtask

  // This task will check for any sideload keys that have been provided
  // TODO: use this for error case instead
  virtual task process_sideload_key();
  /*
    @(negedge cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          forever begin
            // Wait for a valid sideloaded key
            cfg.keymgr_sideload_agent_cfg.vif.wait_valid(logic'(1'b1));

            // Once valid sideload keys have been seen, update scoreboard state.
            //
            // Note: max size of sideloaded key is keymgr_pkg::KeyWidth

            sideload_key = cfg.keymgr_sideload_agent_cfg.vif.sideload_key;

            `uvm_info(`gfn, $sformatf("detected valid sideload_key: %0p", sideload_key), UVM_HIGH)

            for (int i = 0; i < keymgr_pkg::KeyWidth / 32; i++) begin
              keymgr_keys[0][i] = sideload_key.key[0][i*32 +: 32];
              keymgr_keys[1][i] = sideload_key.key[1][i*32 +: 32];
            end

            // Sequence will drop the sideloaded key after scb can process the digest
            cfg.keymgr_sideload_agent_cfg.vif.wait_valid(logic'(1'b0));
          end
          ,
          wait(cfg.under_reset);
      )
    end
    */
  endtask

  // Get sideload keys, pack and return the keys.
  virtual function bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] get_keymgr_keys();
    bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] keymgr_keys;
    keymgr_pkg::hw_key_req_t sideload_key;

    if (cfg.keymgr_sideload_agent_cfg.vif.sideload_key.valid) begin
      sideload_key = cfg.keymgr_sideload_agent_cfg.vif.sideload_key;
      `uvm_info(`gfn, $sformatf("get valid sideload_key: %0p", sideload_key), UVM_HIGH)
      for (int i = 0; i < keymgr_pkg::KeyWidth / 32; i++) begin
        keymgr_keys[0][i] = sideload_key.key[0][i*32 +: 32];
        keymgr_keys[1][i] = sideload_key.key[1][i*32 +: 32];
      end
      return keymgr_keys;
    end else begin
      `uvm_error(`gfn, "Invalid sideload key")
      return 0;
    end
  endfunction

  // This task checks for the start of a KMAC_APP operation and updates scoreboard state
  // accordingly.
  //
  // `process_kmac_app_req_fifo()` cannot be used for this purpose because the scb will only
  // receive a kmac_app_req item once the full request has been completed, which can consist of
  // many different request transactions.
  virtual task detect_kmac_app_start();
    @(negedge cfg.under_reset);
    forever begin
      `DV_SPINWAIT_EXIT(
          forever begin
            // If we are not in KMAC_APP mode, the next time we see valid is the start
            // of a KMAC_APP operation.
            //
            // Assume that application interface requests do not collide.
            `uvm_info(`gfn, "waiting for new kmac_app request", UVM_HIGH)
            wait(!in_kmac_app && app_fsm_active &&
                 (`KMAC_APP_VALID_TRANS(AppKeymgr) ||
                  `KMAC_APP_VALID_TRANS(AppLc) ||
                  `KMAC_APP_VALID_TRANS(AppRom)));
            in_kmac_app = 1;
            sha3_idle = 0;
            sha3_absorb = 1;

            `uvm_info(`gfn, "Raised in_kmac_app and sha3_absorb. Dropped sha3_idle.", UVM_HIGH)

            // we need to choose the correct application interface
            if (`KMAC_APP_VALID_TRANS(AppKeymgr)) begin
              app_mode = AppKeymgr;
              strength = sha3_pkg::L256;
              if (entropy_ready) incr_and_predict_hash_cnt();
            end else if (`KMAC_APP_VALID_TRANS(AppLc)) begin
              app_mode = AppLc;
              strength = sha3_pkg::L128;
            end else if (`KMAC_APP_VALID_TRANS(AppRom)) begin
              app_mode = AppRom;
              strength = sha3_pkg::L256;
            end

            // sample sideload-related coverage
            if (cfg.en_cov) begin
              // Note that all arguments to the covergroup sample() function are the same,
              // this is due to the nature of the arguments that this function takes:
              //
              // - `en_sideload`: this bit indicates whether sideloading mode is active
              // - `in_kmac`    : this bit indicates whether we are operating in KMAC mode
              // - `app_keymgr` : this bit indicates whether we are using the Keymgr-specific App
              //                  interface
              //
              // Checking whether the current application mode is the AppKeymgr mode gives us
              // sufficient information for all three of these arguments due to the nature of this
              // particular interface.
              cov.sideload_cg.sample(app_mode == AppKeymgr,
                                     app_mode == AppKeymgr,
                                     app_mode == AppKeymgr);
            end

            @(posedge sha3_idle);
          end
          ,
          wait(cfg.under_reset || kmac_err.code == ErrKeyNotValid ||
               cfg.kmac_vif.lc_escalate_en_i != lc_ctrl_pkg::Off)
      )
      if (cfg.under_reset || cfg.kmac_vif.lc_escalate_en_i != lc_ctrl_pkg::Off) begin
        @(negedge cfg.under_reset);
      end
      if (kmac_err.code == ErrKeyNotValid) begin
        `uvm_info(`gfn, "kmac_err.code is ErrKeyNotValid", UVM_HIGH)
        `uvm_info(`gfn, "waiting for error to drop", UVM_HIGH)
        wait(kmac_err.code == ErrNone);
        `uvm_info(`gfn, "ErrKeyNotValid has been handled", UVM_HIGH)
      end
      wait(!cfg.under_reset);
    end
  endtask

  // This task models the internal FSM of kmac_app module,
  // required for error handling SW output.
  virtual task process_kmac_app_fsm();
    @(negedge cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          forever begin
            app_mux_sel = SelNone;
            case (app_st)
              StIdle: begin
                app_fsm_active = 0;
                if (!in_kmac_app &&
                    (cfg.m_kmac_app_agent_cfg[AppKeymgr].vif.req_data_if.valid ||
                     cfg.m_kmac_app_agent_cfg[AppLc].vif.req_data_if.valid ||
                     cfg.m_kmac_app_agent_cfg[AppRom].vif.req_data_if.valid)) begin
                  app_st = StAppCfg;
                  app_fsm_active = 1;
                end else if (checked_kmac_cmd == CmdStart) begin
                  app_st = StSw;
                end
              end
              StAppCfg: begin
                if (app_mode == AppKeymgr &&
                    !cfg.keymgr_sideload_agent_cfg.vif.sideload_key.valid) begin
                  app_st = StKeyMgrErrKeyNotValid;
                end else begin
                  app_st = StAppMsg;
                end
              end
              StAppMsg: begin
                app_mux_sel = SelApp;
                if (kmac_app_last) begin
                  if (app_mode == AppKeymgr) begin
                    app_st = StAppOutLen;
                  end else begin
                    app_st = StAppProcess;
                  end
                end
              end
              StAppOutLen: begin
                app_mux_sel = SelOutLen;
                app_st = StAppProcess;
              end
              StAppProcess: begin
                app_st = StAppWait;
              end
              StAppWait: begin
                if (keccak_complete_cycle) begin
                  app_st = StIdle;
                  app_fsm_active = 0;
                end
              end
              StSw: begin
                app_mux_sel = SelSw;
                if (checked_kmac_cmd == CmdDone) begin
                  app_st = StIdle;
                  app_fsm_active = 0;
                end
              end
              StKeyMgrErrKeyNotValid: begin
                app_st = StError;
                app_fsm_active = 0;
                in_kmac_app = 0;
                sha3_squeeze = 0;
                sha3_idle = 1;

                kmac_err.valid = 1;
                kmac_err.code = kmac_pkg::ErrKeyNotValid;
                kmac_err.info = '0;

                predict_err(.is_kmac_err(1));
              end
              StError: begin

                if (`gmv(ral.cfg_shadowed.err_processed)) begin
                  app_st = StIdle;
                end else begin
                  app_st = StError;
                end

                // It's possible for SW to not clear the error until after the hash is done.
                // In this case the hash will be garbage data, so do not check it.
                if (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid &&
                    cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.last) begin
                  do_check_digest = 0;
                end

              end
              default: begin
                app_st = StIdle;
                app_fsm_active = 0;
              end
            endcase
            if (cfg.kmac_vif.lc_escalate_en_i != lc_ctrl_pkg::Off) app_st = StError;
            cfg.clk_rst_vif.wait_clks(1);
            #0;
          end
          ,
          wait(cfg.under_reset);
      )
    end
  endtask

  // This task continuously checks the analysis_port of the push_pull_agent
  // in the kmac_app_agent, as we need to know every time a data block is sent
  // over the KMAC_APP interface.
  virtual task process_kmac_app_req_fifo();
    push_pull_agent_pkg::push_pull_item#(
      .HostDataWidth(kmac_app_agent_pkg::KMAC_REQ_DATA_WIDTH)) kmac_app_block_item;
    forever begin
        wait(!cfg.under_reset);
        @(posedge in_kmac_app);
        `uvm_info(`gfn, $sformatf("req app_mode: %0s", app_mode.name()), UVM_HIGH)
        `DV_SPINWAIT_EXIT(
            forever begin
              kmac_app_req_fifo[app_mode].get(kmac_app_block_item);
              `uvm_info(`gfn,
                        $sformatf("Detected KMAC_APP data transfer:\n%0s",
                                  kmac_app_block_item.sprint()),
                        UVM_HIGH)
              {kmac_app_block_data, kmac_app_block_strb, kmac_app_last} =
                  kmac_app_block_item.h_data;
              kmac_app_block_strb_size = $countones(kmac_app_block_strb);

              // sample coverage
              if (cfg.en_cov) begin
                cov.app_cg_wrappers[app_mode].app_sample(0,
                    kmac_app_block_strb,
                    0,
                    kmac_app_last,
                    in_keccak_rounds);
              end

              while (kmac_app_block_strb > 0) begin
                if (kmac_app_block_strb[0]) begin
                  kmac_app_msg.push_back(kmac_app_block_data[7:0]);
                end
                kmac_app_block_data = kmac_app_block_data >> 8;
                kmac_app_block_strb = kmac_app_block_strb >> 1;
              end
              `uvm_info(`gfn, $sformatf("kmac_app_msg: %0p", kmac_app_msg), UVM_HIGH)
            end
            ,
            wait(cfg.under_reset || !in_kmac_app);
        )
    end
  endtask

  // This task processes the `kmac_app_rsp_fifo`.
  //
  // This fifo is populated once the KMAC has sent the response digest to
  // complete the KMAC_APP request.
  // As such, `in_kmac_app` must always be 1 when a response item is seen, otherwise
  // something has gone horribly wrong.
  //
  // It is important to note that when in KMAC_APP mode, any messages/keys/commands sent
  // to the CSRs will not be considered as valid, so this task needs to take care of checking
  // the KMAC_APP digest and clearing internal state for the next hash operation.
  virtual task process_kmac_app_rsp_fifo();
    kmac_app_item kmac_app_rsp;
    @(negedge cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      `DV_SPINWAIT_EXIT(
          forever begin
            wait(!cfg.under_reset);
            @(posedge in_kmac_app);
            `uvm_info(`gfn, $sformatf("rsp app_mode: %0s", app_mode.name()), UVM_HIGH)
            `DV_SPINWAIT_EXIT(
                bit app_intf_err = 0;
                kmac_app_rsp_fifo[app_mode].get(kmac_app_rsp);
                `uvm_info(`gfn,
                          $sformatf("Detected a KMAC_APP response:\n%0s",
                                    kmac_app_rsp.sprint()),
                          UVM_HIGH)

                // sample coverage
                if (cfg.en_cov) begin
                  cov.app_cg_wrappers[app_mode].app_sample(
                    kmac_app_rsp.byte_data_q.size() <= keymgr_pkg::KmacDataIfWidth/8,
                    '0,
                    kmac_app_rsp.rsp_error,
                    1,
                    0
                  );
                  cov.app_cg_wrappers[app_mode].app_cfg_reg_sample(hash_mode);
                end

                // safety check that things are working properly and
                // no random KMAC_APP operations are seen
                `DV_CHECK_FATAL(in_kmac_app == 1,
                    "in_kmac_app is not set, scoreboard has not picked up KMAC_APP request")

                // Check app interface errors.
                if (app_mode == AppKeymgr && cfg.enable_masking && !entropy_ready) begin
                  app_intf_err = 1;
                  `DV_CHECK_FATAL(kmac_app_rsp.rsp_digest_share0 == 0,
                    "APP interface error, expect output to be all 0s")
                  `DV_CHECK_FATAL(kmac_app_rsp.rsp_digest_share1 == 0,
                    "APP interface error, expect output to be all 0s")
                end else begin

                  // assign digest values
                  kmac_app_digest_share0 = kmac_app_rsp.rsp_digest_share0;
                  kmac_app_digest_share1 = kmac_app_rsp.rsp_digest_share1;

                  if (do_check_digest) check_digest();
                end

                `DV_CHECK_FATAL(kmac_app_rsp.rsp_error == app_intf_err)


                in_kmac_app = 0;
                sha3_squeeze = 0;
                sha3_absorb = 0;
                sha3_idle = 1;
                `uvm_info(`gfn, "dropped in_kmac_app and raised sha3_idle", UVM_HIGH)

                clear_state();
                ,
                wait(!in_kmac_app);
            )
          end
          ,
          wait(cfg.under_reset);
      )
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    dv_base_reg dv_base_csr;

    string csr_name = "";

    bit msgfifo_access;
    bit share0_access;
    bit share1_access;

    bit     do_read_check         = 1'b1;
    bit     write                 = item.is_write();
    uvm_reg_addr_t csr_addr       = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] csr_addr_mask = ral.get_addr_mask();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_base_csr, csr)

      csr_name = csr.get_name();

      // if incoming access is a write to valid csr, immediately make updates
      if (addr_phase_write) begin

        // following csrs are locked by CFG_REGWEN:
        // - cfg
        // - entropy_period
        // - entropy_seed
        // - key_len
        // if writes to these csrs are seen, must check that they are not locked first.
        if (ral.cfg_regwen.locks_reg_or_fld(dv_base_csr) &&
            `gmv(ral.cfg_regwen) == 0) return;

        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_FIFO_BASE : KMAC_FIFO_END]}) begin
      // msgfifo window
      msgfifo_access = 1;
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_STATE_SHARE0_BASE :
                                                     KMAC_STATE_SHARE0_END]}) begin
      // state window 0
      share0_access = 1;
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_STATE_SHARE1_BASE :
                                                     KMAC_STATE_SHARE1_END]}) begin
      // state window 1
      share1_access = 1;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
      // add individual case item for each csr
      "intr_state": begin
        `uvm_info(`gfn, $sformatf("intr_kmac_done: %0d", intr_kmac_done), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("intr_fifo_empty: %0d", intr_fifo_empty), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("intr_kmac_err: %0d", intr_kmac_err), UVM_HIGH)

        if (data_phase_write) begin
          // clear internal state on a write
          if (item.a_data[KmacDone])      intr_kmac_done = 0;
          if (item.a_data[KmacFifoEmpty]) intr_fifo_empty = 0;
          if (item.a_data[KmacErr])       intr_kmac_err = 0;
        end else if (data_phase_read) begin
          // TODO: check below
          do_read_check = 0;
          if (item.d_data[KmacDone]) begin
            sha3_absorb = 0;
            sha3_squeeze = 1;
          end
          // sample intr coverage
          if (cfg.en_cov) begin
            bit [TL_DW-1:0]        intr_en  = `gmv(ral.intr_enable);
            bit [KmacNumIntrs-1:0] intr_exp = `gmv(ral.intr_state);
            foreach (intr_exp[i]) begin
              cov.intr_cg.sample(i, intr_en[i], item.d_data);
              cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
            end
          end
        end
      end
      "intr_enable": begin
        // no need to do anything here, functionality is tested in the automated intr tests,
        // and any issues here will become known if any checks on `intr_state` fail
      end
      "intr_test": begin
        if (addr_phase_write) begin
          bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
          bit [KmacNumIntrs-1:0] intr_exp = item.a_data | `gmv(ral.intr_state);

          void'(ral.intr_state.predict(.value(intr_exp), .kind(UVM_PREDICT_DIRECT)));

          // update internal interrupt tracking variables
          if (intr_exp[KmacDone]) intr_kmac_done = 1;
          if (intr_exp[KmacFifoEmpty]) intr_fifo_empty = 1;
          if (intr_exp[KmacErr]) intr_kmac_err = 1;

          // sample coverage
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
      end
      "cfg_regwen": begin
        // do nothing
      end
      "cfg_shadowed": begin
        // don't continue if the write is shadow register's first write,
        // or the second write has update error
        if (addr_phase_write &&
            (dv_base_csr.is_staged() || dv_base_csr.get_shadow_update_err())) begin
          return;
        end
        if (addr_phase_write) begin
          // don't continue if the KMAC is currently operating
          if (!sha3_idle) begin
            return;
          end

          kmac_en              = item.a_data[KmacEn];
          entropy_fast_process = item.a_data[KmacFastEntropy];
          entropy_ready        = item.a_data[KmacEntropyReady];
          sideload_en          = item.a_data[KmacSideload];

          hash_mode = sha3_pkg::sha3_mode_e'(item.a_data[KmacModeMSB:KmacModeLSB]);

          strength = sha3_pkg::keccak_strength_e'(item.a_data[KmacStrengthMSB:KmacStrengthLSB]);

          entropy_mode = entropy_mode_e'(item.a_data[KmacEntropyModeMSB:KmacEntropyModeLSB]);

          // sample sideload-related coverage
          if (cfg.en_cov) begin
            cov.sideload_cg.sample(sideload_en, kmac_en, 0);
          end

          // Entropy mode configuration error
          if (cfg.enable_masking && !(entropy_mode inside {EntropyModeSw, EntropyModeEdn})) begin
            kmac_err.valid = 1;
            kmac_err.code  = kmac_pkg::ErrIncorrectEntropyMode;
            kmac_err.info  = 24'(entropy_mode);

            predict_err(.is_kmac_err(1));
          end

          if (item.a_data[KmacEntropyReady] && first_op_after_rst) begin
            set_entropy_fetch(1);
          end
        end
      end
      "cmd": begin
        // Writing to CMD will always result in the KMAC doing something
        //
        // TODO - handle error cases
        if (addr_phase_write) begin
          bit [KmacCmdIdx:0] kmac_cmd = item.a_data[KmacCmdIdx:0];

          // Handle hash_cnt clear conditions
          if (item.a_data[KmacHashCntClrIdx]) `DV_CHECK(ral.entropy_refresh_hash_cnt.predict(0));
          if (item.a_data[KmacEntropyReqIdx]) begin
            `DV_CHECK(ral.entropy_refresh_hash_cnt.predict(0));
            set_entropy_fetch(1);
          end

          if (app_fsm_active) begin
            // As per designer comment in https://github.com/lowRISC/opentitan/issues/7716,
            // if CmdStart is sent during an active App operation, KMAC will throw
            // ErrSwIssuedCmdInAppActive, but for any other command the KMAC will throw a
            // ErrSwCmdSequence.
            if (kmac_cmd_e'(kmac_cmd) != CmdNone) begin
              kmac_err.valid = 1;
              kmac_err.code  = kmac_pkg::ErrSwIssuedCmdInAppActive;
              kmac_err.info  = 24'(item.a_data);
              predict_err(.is_kmac_err(1));
            end
          end else begin
            case (kmac_cmd_e'(kmac_cmd))
              CmdStart: begin
                bit en_unsupported_modestrength = 1;

                // Mode/Strength configuration error
                if ((hash_mode inside {sha3_pkg::Shake, sha3_pkg::CShake} &&
                      !(strength inside {sha3_pkg::L128, sha3_pkg::L256})) ||
                     (hash_mode == sha3_pkg::Sha3 &&
                      strength == sha3_pkg::L128)) begin
                  kmac_err.valid  = 1;
                  kmac_err.code   = kmac_pkg::ErrUnexpectedModeStrength;
                  kmac_err.info   = {8'h2, 10'h0, 2'(hash_mode), 1'b0, 3'(strength)};

                  predict_err(.is_kmac_err(1));

                  // If the mode/strength are mis-configured, the IP will finish running a hash
                  // with the incorrect configuration, producing a garbage digest that should not
                  // be checked.
                  if (`gmv(ral.cfg_shadowed.en_unsupported_modestrength)) do_check_digest = 1'b0;
                  else en_unsupported_modestrength = 0;
                end

                if (checked_kmac_cmd == CmdNone && en_unsupported_modestrength) begin
                  // the first 6B of the prefix (function name),
                  // need to check that it is "KMAC" when `kmac_en == 1`
                  bit [47:0] function_name_6B;
                  bit [TL_DW-1:0] prefix_val;

                  // msgfifo will now be written
                  unchecked_kmac_cmd = CmdStart;

                  function_name_6B[31:0]  = `gmv(ral.prefix[0]);
                  prefix_val = `gmv(ral.prefix[1]);
                  function_name_6B[47:32] = prefix_val[15:0];

                  void'(ral.cfg_regwen.predict(.value(0)));

                  // If masking on and it is a KMAC transaction with secret keys, increment the
                  // entropy count.
                  if (kmac_en) incr_and_predict_hash_cnt();

                  if (kmac_en && function_name_6B != kmac_pkg::EncodedStringKMAC) begin
                    kmac_err.valid  = 1;
                    kmac_err.code   = kmac_pkg::ErrIncorrectFunctionName;
                    kmac_err.info   = {8'h1, 16'h0};

                    // If incorrect function name is given, KMAC will finish the current hash
                    // operation and produce an incorrect digest, do not check this.
                    predict_err(.is_kmac_err(1));

                    do_check_digest = 0;
                  end
                end else begin // SW sent wrong command

                  kmac_err.valid = 1;
                  kmac_err.code  = kmac_pkg::ErrSwCmdSequence;
                  kmac_err.info  = get_kmac_sw_cmd_seq_err_info(kmac_cmd);

                  predict_err(.is_kmac_err(1));
                end
              end
              CmdProcess: begin
                if (checked_kmac_cmd == CmdStart) begin
                  // kmac will now compute the digest
                  unchecked_kmac_cmd = CmdProcess;
                end else begin // SW sent wrong command
                  kmac_err.valid = 1;
                  kmac_err.code  = kmac_pkg::ErrSwCmdSequence;
                  kmac_err.info  = get_kmac_sw_cmd_seq_err_info(kmac_cmd);

                  predict_err(.is_kmac_err(1));
                end
              end
              CmdManualRun: begin
                if (checked_kmac_cmd inside {CmdProcess, CmdManualRun}) begin
                  // kmac will now squeeze more output data
                  unchecked_kmac_cmd = CmdManualRun;

                  req_manual_squeeze = 1;
                  // Mask out status sequeeze check because it requires cycle accurate prediction.
                  // Use sequence to backdoor check if sequeeze is reset to 0 after each squeeze
                  // command.
                  status_mask[KmacStatusSha3Squeeze] = 1;
                  `uvm_info(`gfn, "raised req_manual_squeeze", UVM_HIGH)
                end else begin // SW sent wrong command
                  kmac_err.valid = 1;
                  kmac_err.code  = kmac_pkg::ErrSwCmdSequence;
                  kmac_err.info  = get_kmac_sw_cmd_seq_err_info(kmac_cmd);

                  predict_err(.is_kmac_err(1));
                end
              end
              CmdDone: begin
                if (checked_kmac_cmd inside {CmdProcess, CmdManualRun}) begin
                  unchecked_kmac_cmd = CmdDone;

                  sha3_squeeze = 0;
                  `uvm_info(`gfn, "dropped sha3_squeeze", UVM_HIGH)

                  // sample coverage of message length
                  if (cfg.en_cov) begin
                    cov.msg_len_cg.sample(msg.size());
                  end

                  status_mask[KmacStatusSha3Squeeze] = 0;

                  // Calculate the digest using DPI and check for correctness
                  if (do_check_digest) check_digest();

                  // Flush all scoreboard state to prepare for the next hash operation
                  clear_state();

                  void'(ral.cfg_regwen.predict(.value(1)));

                end else begin // SW sent wrong command

                  kmac_err.valid = 1;
                  kmac_err.code  = kmac_pkg::ErrSwCmdSequence;
                  kmac_err.info  = get_kmac_sw_cmd_seq_err_info(kmac_cmd);

                  predict_err(.is_kmac_err(1));
                end
              end
              CmdNone: begin
                // RTL internal value, doesn't actually do anything
              end
              default: begin
                `uvm_fatal(`gfn, $sformatf("%0d is an illegal CMD value", kmac_cmd))
              end
            endcase
          end
        end else begin
          // this bit will be set to 0 during the data phase of the write,
          // providing better detection of when exactly a manual squeeze command
          // has been requested
          req_manual_squeeze = 0;
          `uvm_info(`gfn, "dropped req_manual_squeeze", UVM_HIGH)
        end
      end
      "status": begin
        if (addr_phase_read) begin
          bit [TL_DW-1:0] exp_status;

          exp_status[KmacStatusSha3Idle]    = sha3_idle;
          exp_status[KmacStatusSha3Absorb]  = sha3_absorb;
          exp_status[KmacStatusSha3Squeeze] = sha3_squeeze;


          void'(ral.status.predict(.value(exp_status), .kind(UVM_PREDICT_READ)));

        end else if (data_phase_read) begin
          do_read_check = 0;

          // Check fifo empty/full and fifo depth are aligned.
          if (item.d_data[KmacStatusFifoEmpty]) begin
            `DV_CHECK_EQ(item.d_data[KmacStatusFifoDepthMSB : KmacStatusFifoDepthLSB], 0,
                 $sformatf("Status (val:%0h) error when fifo empty! Expect Fifo Depth to be 0",
                 item.d_data))
            `DV_CHECK_EQ(item.d_data[KmacStatusFifoFull], 0,
                 $sformatf("Status (val:%0h) error! Full/Empty cannot both set",
                 item.d_data))
          end else if (item.d_data[KmacStatusFifoFull]) begin
            `DV_CHECK_EQ(item.d_data[KmacStatusFifoDepthMSB : KmacStatusFifoDepthLSB],
                 KMAC_FIFO_DEPTH,
                 $sformatf("Status (val:%0h) error when fifo full! Expect Fifo Depth to be %0h",
                 item.d_data, KMAC_FIFO_DEPTH))
          end else begin
            // When fifo empty is not set, we still allow one clock cycle where the fifo depth is
            // set to 0. This is documented in issue #14286.
            `DV_CHECK_LT(item.d_data[KmacStatusFifoDepthMSB : KmacStatusFifoDepthLSB],
                 KMAC_FIFO_DEPTH,
                 $sformatf("Status (val:%0h) error! Depth cannot be %0h when fifo full is not set",
                 item.d_data, KMAC_FIFO_DEPTH))
          end
          `DV_CHECK_EQ(csr.get_mirrored_value() | status_mask, item.d_data | status_mask,
                       $sformatf("reg name: %0s", csr.get_full_name()))

          // Sample coverage:
          if (cfg.en_cov) begin
            cov.msgfifo_level_cg.sample(
                item.d_data[KmacStatusFifoEmpty],
                item.d_data[KmacStatusFifoFull],
                item.d_data[KmacStatusFifoDepthMSB : KmacStatusFifoDepthLSB],
                hash_mode,
                is_kmac_en());
            cov.sha3_status_cg.sample(item.d_data[KmacStatusSha3Idle],
                                      item.d_data[KmacStatusSha3Absorb],
                                      item.d_data[KmacStatusSha3Squeeze]);
          end
        end
      end
      "key_len": begin
        // TODO need to do error checking
        if (addr_phase_write) begin
          key_len = key_len_e'(item.a_data);
        end
      end
      "err_code": begin
        if (data_phase_read) begin
          kmac_pkg::err_t err_code = kmac_pkg::err_t'(item.d_data);
          if (err_code.code == ErrSwCmdSequence) begin
            // Mask out the kmac_state FSM information because the SCB is not cycle accurate to
            // track in which SHA state does the error happen.
            kmac_pkg::err_t err_chk_mask = '1;
            err_chk_mask.info[kmac_st_idx +: 2] = 0;
            // TODO: add some direct sequence to check this error information.
            do_read_check = 0;
            `DV_CHECK_EQ(csr.get_mirrored_value() & err_chk_mask, item.d_data & err_chk_mask,
                         $sformatf("reg name: %0s", csr.get_full_name()))
          end
        end
      end
      "entropy_refresh_threshold_shadowed": begin
        if (addr_phase_write &&
            (dv_base_csr.is_staged() || dv_base_csr.get_shadow_update_err())) begin
          bit [HASH_CNT_WIDTH-1:0] threshold = item.a_data;
          if (threshold > 0 && threshold <= `gmv(ral.entropy_refresh_hash_cnt)) begin
            `DV_CHECK(ral.entropy_refresh_hash_cnt.predict(0));
            set_entropy_fetch(1);
          end
        end
      end
      "entropy_period": begin
        if (cfg.en_cov && addr_phase_write) begin
          cov.entropy_timer_cg.sample(item.a_data[9:0], item.a_data[31:16],
                                      entropy_mode == EntropyModeEdn);
        end
      end
      default: begin
        // regex match the key_share csrs
        string full_idx;
        string split_idx[$];
        string key_share;
        string key_idx;

        // KEY_SHARE csrs
        if (!uvm_re_match("key_share*", csr_name)) begin
          full_idx = csr_name.substr(9, csr_name.len()-1);
          str_utils_pkg::str_split(full_idx, split_idx, "_");
          // safety check that the regex is working correctly
          `DV_CHECK_FATAL(split_idx.size() == 2,
              $sformatf("%0s does not contain a correct key index!", full_idx))
          key_share = split_idx.pop_front();
          key_idx = split_idx.pop_front();

          // If keys are being written, update the scoreboard state
          if (addr_phase_write) begin
            keys[key_share.atoi()][key_idx.atoi()] = item.a_data;
          end
        // PREFIX csrs
        end else if (!uvm_re_match("prefix_*", csr_name)) begin
          str_utils_pkg::str_split(csr_name, split_idx, "_");
          full_idx = split_idx.pop_back();

          if (addr_phase_write) begin
            prefix[full_idx.atoi()] = item.a_data;
          end
        end
      end
    endcase

    ////////////////////////////////////////////
    // Process incoming writes to the msgfifo //
    ////////////////////////////////////////////
    //
    // One problem with the scoreboard only having access to the data written to the msgfifo
    // is that the message is post-fixed with the encoded output length if KMAC mode is used.
    //
    // However there is no way to access it other than to calculate the length of the seen digest.
    // Even though it is somewhat hacky, this is the approach we'll take.
    // If the length of the calculated output is incorrect for whatever reason (scoreboard error
    // or RTL error), then passing this value into the DPI model will result in an incorrect
    // digest comparison.
    if (msgfifo_access) begin
      if (addr_phase_write) begin
        if (in_kmac_app) begin
          kmac_err.valid  = 1;
          kmac_err.code   = kmac_pkg::ErrSwPushedMsgFifo;
          kmac_err.info   = {8'h0, 8'(app_st), 8'(app_mux_sel)};
          predict_err(.is_kmac_err(1));
        end else if (checked_kmac_cmd != CmdStart) begin
          // TODO
          //
          // If we get here we are writing to the msgfifo in an invalid state.
          // Implement error checking here.
        end else if (!cfg.under_reset) begin
          bit [7:0] full_data[4];
          bit [7:0] masked_data[];

          {<< byte {full_data}} = item.a_data;

          `uvm_info(`gfn, $sformatf("item.a_data: 0x%0x", item.a_data), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("item.a_mask: 0b%0b", item.a_mask), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("full_data: %0p", full_data), UVM_HIGH)

          // sample coverage on the write mask
          if (cfg.en_cov) begin
            cov.msgfifo_write_mask_cg.sample(item.a_mask);
          end

          // All writes in big-endian order will be full-word,
          // so we can generalize this to a for-loop that reverses the byte order of each word.
          // This way we can also preserve little-endian ordering.
          for (int i = 0; i < TL_DBW; i++) begin
            if (item.a_mask[i]) begin
              masked_data = `gmv(ral.cfg_shadowed.msg_endianness) ? {full_data[i], masked_data} :
                                                           {masked_data, full_data[i]};
            end
          end
          msg = {msg, masked_data};

          `uvm_info(`gfn, $sformatf("masked_data: %0p", masked_data), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("msg: %0p", msg), UVM_HIGH)
        end
      end
      // indicate that the msgfifo access is now over
      msgfifo_access = 0;
    end

    ///////////////////////////////////////////////////
    // Process incoming reads from the digest window //
    ///////////////////////////////////////////////////

    if (share0_access || share1_access) begin
      bit [TL_DW-1:0] digest_word;
      bit [7:0] digest_byte;
      bit  [TL_DBW-1:0] state_mask;

      `uvm_info(`gfn, $sformatf("share0: %0d", share0_access), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("share1: %0d", share1_access), UVM_HIGH)

      if (data_phase_read) begin
        state_mask = item.a_mask;
        digest_word = item.d_data;

        // sample coverage on state read mask
        if (cfg.en_cov) begin
          cov.state_read_mask_cg.sample(state_mask, share1_access);
        end

        `uvm_info(`gfn, $sformatf("state read mask: 0b%0b", state_mask), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("digest_word: 0x%0x", digest_word), UVM_HIGH)

        if (`gmv(ral.cfg_shadowed.state_endianness)) begin
          digest_word = {<< byte {digest_word}};
          state_mask = {<< bit {state_mask}};

          `uvm_info(`gfn, $sformatf("endian-swapped digest word: 0x%0x", digest_word), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("endian-swapped read mask: 0b%0b", state_mask), UVM_HIGH)
        end
        for (int i = 0; i < TL_DBW; i++) begin
          if (state_mask[i]) begin
            digest_byte = digest_word[i*8 +: 8];
            `uvm_info(`gfn, $sformatf("digest_byte: 0x%0x", digest_byte), UVM_HIGH)

            if (share0_access) begin
              digest_share0 = {digest_share0, digest_byte};
              `uvm_info(`gfn, $sformatf("intermediate digest_share0: %0p", digest_share0), UVM_HIGH)
            end else if (share1_access) begin
              digest_share1 = {digest_share1, digest_byte};
              `uvm_info(`gfn, $sformatf("intermediate digest_share1: %0p", digest_share1), UVM_HIGH)
            end
          end
        end
      end

      // If we read the state digest in either CmdStart or CmdDone states,
      // we should read back all zeroes.
      // Check immediately and clear the digest arrays.
      if (checked_kmac_cmd inside {CmdNone, CmdStart, CmdDone}) begin
        foreach (digest_share0[i]) begin
          `DV_CHECK_EQ_FATAL(digest_share0[i], '0,
              $sformatf("Share 0 should be zero in state %0s", checked_kmac_cmd.name()))
          digest_share0 = {};
        end
        foreach (digest_share1[i]) begin
          `DV_CHECK_EQ_FATAL(digest_share1[i], '0,
              $sformatf("Share 1 should be zero in state %0s", checked_kmac_cmd.name()))
          digest_share1 = {};
        end
      end
      share0_access = 0;
      share1_access = 0;
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read && csr_name != "") begin
      if (!cfg.do_cycle_accurate_check && csr_name inside {"intr_state", "status"}) begin
        do_read_check = 0;
      end
      if (csr_name == "err_code" && cfg.skip_read_check == 1) begin
        do_read_check = 0;
      end
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      `DV_CHECK(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask : process_tl_access

  virtual function void predict_err(bit is_sha3_err = 0, bit is_kmac_err = 0);
    // set interrupt
    if (!intr_kmac_err) intr_kmac_err = 1;
    `uvm_info(`gfn, "raised intr_kmac_err", UVM_HIGH)
    if (is_sha3_err) `uvm_info(`gfn, $sformatf("sha3_err: %0p", sha3_err), UVM_HIGH)
    if (is_kmac_err) `uvm_info(`gfn, $sformatf("kmac_err: %0p", kmac_err), UVM_HIGH)

    // predict error CSR
    if (is_sha3_err) begin
      `DV_CHECK(ral.err_code.predict(.value(TL_DW'(sha3_err)), .kind(UVM_PREDICT_DIRECT)));
    end else if (is_kmac_err) begin
      `DV_CHECK(ral.err_code.predict(.value(TL_DW'(kmac_err)), .kind(UVM_PREDICT_DIRECT)));
    end

    // collect coverage
    if (cfg.en_cov) begin
      cov.error_cg.sample(kmac_err.code, unchecked_kmac_cmd, hash_mode, strength);
    end

    kmac_err = '{valid: 1'b0,
                 code: kmac_pkg::ErrNone,
                 info: '0};
    sha3_err = '{valid: 1'b0,
                 code: sha3_pkg::ErrNone,
                 info: '0};
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    clear_state();

    checked_kmac_cmd   = CmdNone;
    unchecked_kmac_cmd = CmdNone;

    first_op_after_rst = 1;

    // status tracking bits
    sha3_idle     = ral.status.sha3_idle.get_reset();
    sha3_absorb   = ral.status.sha3_absorb.get_reset();
    sha3_squeeze  = ral.status.sha3_squeeze.get_reset();
  endfunction

  // This function should be called to reset internal state to prepare for a new hash operation
  virtual function void clear_state();
    `uvm_info(`gfn, "clearing scoreboard state", UVM_HIGH)

    if (first_op_after_rst) first_op_after_rst = 0;

    do_check_digest = 1;

    msg.delete();
    kmac_app_msg.delete();

    kmac_app_block_data      = '0;
    kmac_app_block_strb      = '0;
    kmac_app_block_strb_size = 0;
    kmac_app_last            = 0;
    in_kmac_app              = 0;

    req_manual_squeeze      = 0;
    msg_digest_done         = 0;

    set_entropy_fetch(0);

    kmac_err = '{valid: 1'b0,
                 code: kmac_pkg::ErrNone,
                 info: '0};
    sha3_err = '{valid: 1'b0,
                 code: sha3_pkg::ErrNone,
                 info: '0};

    app_st = StIdle;

    keys          = '0;
    prefix        = '{default:0};
    digest_share0 = {};
    digest_share1 = {};

    kmac_app_digest_share0 = '0;
    kmac_app_digest_share1 = '0;
  endfunction

  // This function is called whenever a CmdDone command is issued to KMAC,
  // and will compare the seen digest against the digest calculated from the DPI model.
  //
  // Though we don't have direct access to the specified output length for XOF functions,
  // the last byte written to the msgfifo (only for XOFs) will be the number of preceding bytes
  // that encode the requested output length.
  // From this we can decode what the initially requested output length is.
  //
  // We also need to decode what the prefix is (only for KMAC), as only the encoded values
  // are written to the CSRs.  virtual function void check_digest();
  virtual function void check_digest();

    // Cast to an array so we can pass this into the DPI functions
    bit [7:0] msg_arr[];

    // Determines which kmac variant to use
    bit xof_en;

    // Set this to the calculated output length for XOFs
    int output_len_bytes;

    // Array to hold the digest read from the state windows
    bit [7:0] unmasked_digest[];

    // Array to hold the expected digest calculated by DPI model
    bit [7:0] dpi_digest[];

    // Function name and customization strings for KMAC operations
    string fname;
    string custom_str;

    // Use this to store the correct set of keys (SW-provided or sideloaded)
    bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] exp_keys;

    // The actual key used for KMAC operations
    bit [31:0] unmasked_key[$];

    // key byte-stream for the DPI model
    bit [7:0] dpi_key_arr[];

    // Intermediate array for streaming `unmasked_key` into `dpi_key_arr`
    bit [7:0] unmasked_key_bytes[];

    int key_word_len, key_byte_len;

    // Actual hash_mode based on interface or SW register
    sha3_pkg::sha3_mode_e actual_hash_mode = in_kmac_app ? sha3_pkg::CShake : hash_mode;

    bit use_keymgr_keys = sideload_en || (in_kmac_app && app_mode == AppKeymgr);

    if (cfg.en_scb == 0) return;

    if (use_keymgr_keys) key_len = key_len_e'(Key256);
    key_word_len = get_key_size_words(key_len);
    key_byte_len = get_key_size_bytes(key_len);

    `uvm_info(`gfn, $sformatf("key_word_len: %0d", key_word_len), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("key_byte_len: %0d", key_byte_len), UVM_HIGH)

    // Calculate:
    // - the expected output length in bytes
    // - if we are using the xof version of kmac
    if (in_kmac_app) begin
      // KMAC_APP output will always be 384 bits (48 bytes)
      output_len_bytes = AppDigestW / 8;

      // xof_en is 1 when the padded output length is 0,
      // but this will never happen in KMAC_APP
      xof_en = 0;
    end else begin
      get_digest_len_and_xof(output_len_bytes, xof_en, msg);

      // quick check that the calculated output length is the same
      // as the number of bytes read from the digest window
      `DV_CHECK_EQ_FATAL(digest_share0.size(), output_len_bytes,
          $sformatf("Calculated output length(%0d) doesn't match actual output length(%0d)!",
                    output_len_bytes, digest_share0.size()))
    end

    if (cfg.en_cov) begin
      // sample configuration coverage, as only now do we know which KMAC variant is used
      // (xof/non-xof)
      cov.sample_cfg(kmac_en, xof_en, strength, actual_hash_mode, key_len,
                     `gmv(ral.cfg_shadowed.msg_endianness), `gmv(ral.cfg_shadowed.state_endianness),
                     `gmv(ral.cfg_shadowed.sideload), entropy_mode, entropy_fast_process);

      // sample coverage on the digest length
      if (cfg.en_cov) begin
        cov.output_digest_len_cg.sample(output_len_bytes);
      end
    end


    `uvm_info(`gfn, $sformatf("output_len_bytes: %0d", output_len_bytes), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("xof_en: %0d", xof_en), UVM_HIGH)

    // initialize arrays
    dpi_digest = new[output_len_bytes];
    unmasked_digest = new[output_len_bytes];

    /////////////////////////////////
    // Calculate the actual digest //
    /////////////////////////////////
    if (cfg.enable_masking) begin
      if (in_kmac_app) begin
        unmasked_digest = {<< byte {kmac_app_digest_share0 ^ kmac_app_digest_share1}};
      end else begin
        foreach (unmasked_digest[i]) begin
          unmasked_digest[i] = digest_share0[i] ^ digest_share1[i];
        end
      end
    end else begin
      if (in_kmac_app) begin
        unmasked_digest = {<< byte {kmac_app_digest_share0}};
      end else begin
        unmasked_digest = digest_share0;
      end
    end
    `uvm_info(`gfn, $sformatf("unmasked_digest: %0p", unmasked_digest), UVM_HIGH)

    ///////////////////////////////////////////////////////////
    // Calculate the expected digest using the DPI-C++ model //
    ///////////////////////////////////////////////////////////
    if (in_kmac_app) begin
      // kmac_app message is a byte array, cast to bit[7:0]
      msg_arr = new[kmac_app_msg.size()];
      foreach (kmac_app_msg[i]) begin
        msg_arr[i] = kmac_app_msg[i];
      end
    end else begin
      msg_arr = msg;
    end
    `uvm_info(`gfn, $sformatf("msg_arr for DPI mode: %0p", msg_arr), UVM_HIGH)

    case (actual_hash_mode)
      ///////////
      // SHA-3 //
      ///////////
      sha3_pkg::Sha3: begin
        case (strength)
          sha3_pkg::L224: begin
            digestpp_dpi_pkg::c_dpi_sha3_224(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_sha3_256(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L384: begin
            digestpp_dpi_pkg::c_dpi_sha3_384(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L512: begin
            digestpp_dpi_pkg::c_dpi_sha3_512(msg_arr, msg_arr.size(), dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for sha3", strength.name()))
          end
        endcase
      end
      ///////////
      // SHAKE //
      ///////////
      sha3_pkg::Shake: begin
        case (strength)
          sha3_pkg::L128: begin
            digestpp_dpi_pkg::c_dpi_shake128(msg_arr, msg_arr.size(), output_len_bytes, dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_shake256(msg_arr, msg_arr.size(), output_len_bytes, dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for shake", strength.name()))
          end
        endcase
      end
      ////////////
      // CSHAKE //
      ////////////
      sha3_pkg::CShake: begin
        // Get the fname and custom_str string values from the writes to PREFIX csrs
        get_fname_and_custom_str(in_kmac_app, fname, custom_str);

        if (kmac_en) begin
          // Calculate the unmasked key
          exp_keys = use_keymgr_keys ? get_keymgr_keys : keys;
          for (int i = 0; i < key_word_len; i++) begin
            if (cfg.enable_masking || cfg.sw_key_masked || use_keymgr_keys) begin
              unmasked_key.push_back(exp_keys[0][i] ^ exp_keys[1][i]);
            end else begin
              unmasked_key.push_back(exp_keys[0][i]);
            end
            `uvm_info(`gfn, $sformatf("unmasked_key[%0d] = 0x%0x", i, unmasked_key[i]), UVM_HIGH)
          end

          // Convert the key array into a byte array for the DPI model
          unmasked_key_bytes = {<< 32 {unmasked_key}};
          dpi_key_arr = {<< byte {unmasked_key_bytes}};
          `uvm_info(`gfn, $sformatf("dpi_key_arr.size(): %0d", dpi_key_arr.size()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("dpi_key_arr: %0p", dpi_key_arr), UVM_HIGH)

          case (strength)
            sha3_pkg::L128: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac128_xof(msg_arr, msg_arr.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    custom_str,
                                                    output_len_bytes, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac128(msg_arr, msg_arr.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                custom_str,
                                                output_len_bytes, dpi_digest);
              end
            end
            sha3_pkg::L256: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac256_xof(msg_arr, msg_arr.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    custom_str,
                                                    output_len_bytes, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac256(msg_arr, msg_arr.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                custom_str,
                                                output_len_bytes, dpi_digest);
              end
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for kmac", strength.name()))
            end
          endcase
        end else begin
          // regular cshake - used for otp_ctrl/rom_ctrl application interfaces
          case (strength)
            sha3_pkg::L128: begin
              digestpp_dpi_pkg::c_dpi_cshake128(msg_arr, fname, custom_str, msg_arr.size(),
                                                output_len_bytes, dpi_digest);
            end
            sha3_pkg::L256: begin
              digestpp_dpi_pkg::c_dpi_cshake256(msg_arr, fname, custom_str, msg_arr.size(),
                                                output_len_bytes, dpi_digest);
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for cshake", strength.name()))
            end
          endcase
        end
      end
    endcase

    `uvm_info(`gfn, $sformatf("dpi_digest: %0p", dpi_digest), UVM_HIGH)

    /////////////////////////////////////////
    // Compare actual and expected digests //
    /////////////////////////////////////////
    for (int i = 0; i < output_len_bytes; i++) begin
      `DV_CHECK_EQ_FATAL(unmasked_digest[i], dpi_digest[i],
          $sformatf("Mismatch between unmasked_digest[%0d] and dpi_digest[%0d]", i, i))
    end

  endfunction

  // This function is used to calculate the requested digest length
  virtual function void get_digest_len_and_xof(ref int output_len, ref bit xof_en,
                                               ref bit [7:0] msg[$]);
    xof_en = 0;
    case (hash_mode)
      // For SHA3 hashes, the output length is the same as the security strength.
      sha3_pkg::Sha3: begin
        case (strength)
          sha3_pkg::L224: begin
            output_len = 224 / 8; // 28
          end
          sha3_pkg::L256: begin
            output_len = 256 / 8; // 32
          end
          sha3_pkg::L384: begin
            output_len = 384 / 8; // 48
          end
          sha3_pkg::L512: begin
            output_len = 512 / 8; // 64
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for sha3", strength.name()))
          end
        endcase
      end
      // For Shake hashes, the output length isn't encoded anywhere,
      // so we just return the length of the state digest array.
      sha3_pkg::Shake: begin
        output_len = digest_share0.size();
      end
      // CShake is where things get more interesting.
      // We need to essentially decode the encoded output length that is
      // written to the msgfifo as a post-fix to the actual message.
      sha3_pkg::CShake: begin
        bit [MAX_ENCODE_WIDTH-1:0] full_len = '0;
        // the very last byte written to msgfifo is the number of bytes that
        // when put together represent the encoded output length.
        bit [7:0] num_encoded_byte = msg.pop_back();

        for (int i = 0; i < num_encoded_byte; i++) begin
          full_len[i*8 +: 8] = msg.pop_back();
        end

        // We should set xof_en if `right_encode(0)` was written to the msgfifo after the message.
        // right_encode(0) = '{'h0, 'h1}
        if (num_encoded_byte == 1 && full_len == 0) begin
          xof_en = 1;
          // can't set  the output length to 0, so we fall back to the Shake behavior here
          output_len = digest_share0.size();
        end else begin
          output_len = full_len / 8;
        end
      end
    endcase
  endfunction

  // This function is used to calculate the fname and custom_str string values
  // from the data written to the PREFIX csrs
  //
  // Strings are encoded as:
  //  `encode_string(S) = left_encode(len(S)) || S`
  virtual function void get_fname_and_custom_str(bit en_kmac_app,
                                                 ref string fname,
                                                 ref string custom_str);
    bit [7:0] prefix_bytes[$];
    // The very first byte of each encoded string represents the number of bytes
    // that make up the encoded string's length.
    bit [7:0] num_enc_bytes_of_str_len;

    bit [16:0] str_len;

    byte fname_arr[];
    byte custom_str_arr[];

    if (en_kmac_app && kmac_pkg::AppCfg[app_mode].PrefixMode) begin
      prefix_bytes = {<< byte {kmac_pkg::AppCfg[app_mode].Prefix}};
    end else begin
      prefix_bytes = {<< 32 {prefix}};
      prefix_bytes = {<< byte {prefix_bytes}};
    end

    // sample coverage
    if (cfg.en_cov) begin
      foreach (prefix_bytes[i]) begin
        cov.prefix_range_cg.sample(byte'(prefix_bytes[i]));
      end
    end

    `uvm_info(`gfn, $sformatf("prefix: %0p", prefix), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("prefix_bytes: %0p", prefix_bytes), UVM_HIGH)

    // fname comes first in the PREFIX registers

    // This value should be 1
    num_enc_bytes_of_str_len = prefix_bytes.pop_front();
    `DV_CHECK_EQ(num_enc_bytes_of_str_len, 1,
        $sformatf("Only one byte should be used to encode len(fname)"))

    // The string length is always in terms of bits, need to convert to byte length
    str_len = prefix_bytes.pop_front() / 8;

    fname_arr  = new[str_len];
    for (int i = 0; i < str_len; i++) begin
      fname_arr[i] = byte'(prefix_bytes.pop_front());
    end

    // custom_str is next

    num_enc_bytes_of_str_len = prefix_bytes.pop_front();

    // convert string length to length in bytes
    for (int i = 0; i < num_enc_bytes_of_str_len; i++) begin
      str_len[(num_enc_bytes_of_str_len  - i - 1)*8 +: 8] = prefix_bytes.pop_front();
    end
    str_len /= 8;

    custom_str_arr = new[str_len];
    for (int i = 0; i < str_len; i++) begin
      custom_str_arr[i] = byte'(prefix_bytes.pop_front());
    end

    // Convert the byte arrays into strings
    fname = str_utils_pkg::bytes_to_str(fname_arr);
    custom_str = str_utils_pkg::bytes_to_str(custom_str_arr);

    `uvm_info(`gfn, $sformatf("decoded fname: %0s", fname), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("decoded custom_str: %0s", custom_str), UVM_HIGH)
  endfunction

  // Return `info` field for ErrSwCmdSequence with the current kmac_cmd as input.
  // This scb do not predict kmac internal state, so the FSM state information is all 0 and will be
  // masked out during read check.
  function kmac_sw_cmd_seq_err_info_t get_kmac_sw_cmd_seq_err_info(bit [KmacCmdIdx:0] kmac_cmd);
    kmac_sw_cmd_seq_err_info_t err_info;
    err_info.sw_cmd = kmac_cmd;
    err_info.sw_err = 1;
    return err_info;
  endfunction

  // Increment the hash_cnt under the following conditions:
  // 1). Masking mode is On
  // 2). Hash_cnt is less than the threshold (except threshold == 0)
  // 3). Hash_cnt is not overflowed
  function void incr_and_predict_hash_cnt();
    bit [HASH_CNT_WIDTH-1:0] curr_hash_cnt_val = `gmv(ral.entropy_refresh_hash_cnt);
    if (cfg.enable_masking == 0) return;

    // Check overflow
    if (curr_hash_cnt_val != '1) begin
      bit [HASH_CNT_WIDTH-1:0] new_hash_cnt_val = curr_hash_cnt_val + 1;

      // Check threshold
      if (new_hash_cnt_val >= `gmv(ral.entropy_refresh_threshold_shadowed) &&
          `gmv(ral.entropy_refresh_threshold_shadowed) > 0) begin
        `DV_CHECK(ral.entropy_refresh_hash_cnt.predict(0));
      end else begin
        `DV_CHECK(ral.entropy_refresh_hash_cnt.predict(new_hash_cnt_val));
      end
    end
  endfunction

  function void set_entropy_fetch(bit val);
    if (val) begin
      if (entropy_mode == EntropyModeEdn) in_edn_fetch = cfg.enable_masking;
    end else begin
      in_edn_fetch = 0;
      `uvm_info(`gfn, "dropped in_edn_fetch", UVM_HIGH)
    end
  endfunction

  function bit is_kmac_en();
    return in_kmac_app ? app_mode == AppKeymgr : kmac_en;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass

`undef CALC_PARTIAL_MSG

`undef KMAC_APP_VALID_TRANS
