// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_scoreboard extends cip_base_scoreboard #(.CFG_T (hmac_env_cfg),
                                                    .RAL_T (hmac_reg_block),
                                                    .COV_T (hmac_env_cov));
  `uvm_component_utils(hmac_scoreboard)
  `uvm_component_new

  bit             sha_en, hmac_idle;
  bit             fifo_empty;   // TODO(#23739): remove this line when RTL PR got merged
  bit [7:0]       msg_q[$];
  bit [7:0]       msg_part_q[$];  // Queue containing piece of the message if HASH is interrupted
  bit             hmac_start, hmac_process, hmac_stopped, hmac_continue;
  int             hmac_wr_cnt, hmac_rd_cnt;
  int             fifo_rd_depth;
  int             block_process_cycles;
  int             key_process_cycles;
  bit [TL_DW-1:0] key[NUM_KEYS];
  bit [TL_DW-1:0] exp_digest[NUM_DIGESTS];
  bit [3:0]       previous_digest_size, expected_digest_size;
  bit             invalid_cfg;
  bit [TL_DW-1:0] hmac_status_data;
  bit [5:0]       hmac_fifo_depth;
  bit             hmac_fifo_full;
  bit             fifo_full_detected;
  bit             hmac_fifo_empty;
  bit             fifo_empty_intr;
  bit             hmac_process_last;
  bit             hmac_stopped_last;
  bit             hmac_start_last;
  bit             hmac_continue_last;
  bit [TL_DW-1:0] intr_test;
  bit [TL_DW-1:0] intr_state_exp;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    wait(cfg.under_reset);
    forever begin
      wait(!cfg.under_reset);
      // This isolation fork is needed to ensure that "disable fork" call won't kill any other
      // processes at the same level from the base classes
      fork begin : isolation_fork
        fork
          begin : main_thread
            fork
              hmac_process_fifo_status();
              hmac_process_fifo_wr();
              hmac_process_fifo_rd();
              hmac_intr_test();
              monitor_cov();
            join
            wait fork;  // To ensure it will be killed only when the reset will occur
          end
          begin : reset_thread
            wait(cfg.under_reset);
          end
        join_any
        disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
      end join
    end
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    string  csr_name;
    bit     do_read_check           = 1'b1;
    bit     do_cycle_accurate_check = 1'b1;
    bit     write                   = item.is_write();
    bit [TL_AW-1:0] addr_mask       = ral.get_addr_mask();
    uvm_reg_addr_t  csr_addr        = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();
    // if addr inside msg fifo, no ral model
    end else if (!((item.a_addr & addr_mask) inside {[HMAC_MSG_FIFO_BASE :
                                                      HMAC_MSG_FIFO_LAST_ADDR]})) begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr or mem, then update right away on addr channel
    if (write && channel == AddrChannel) begin
      // push the msg into msg_fifo
      if ((item.a_addr & addr_mask) inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]}) begin
        // Only push message into the FIFO when intended, as in case of S&R triggered with another
        // context, we don't want to process the message of this other context.
        if (!cfg.sar_skip_ctxt) begin
          if ((!sha_en) || (!hmac_start && !hmac_continue)) begin
            update_err_intr_code(SwPushMsgWhenDisallowed);
          end else if (!cfg.under_reset) begin
            bit [7:0] bytes[4];
            bit [7:0] msg[$];
            // Register coverage for the fact that a write occurs to the message FIFO during
            // a compression round
            if (cfg.en_cov) cov.wr_msg_during_hash_cg.sample(1);
            {<<byte{bytes}} = item.a_data;
            // do endian swap in the word according to the mask, then push to the msg queue
            foreach (item.a_mask[i]) begin
              if (item.a_mask[i]) begin
                // endian_swap bit 1 operates at big endian data
                msg = (ral.cfg.endian_swap.get_mirrored_value()) ?
                      {msg, bytes[i]} : {bytes[i], msg};
              end
            end
            foreach (msg[i]) msg_q.push_back(msg[i]);
            update_wr_msg_length(msg_q.size());
          end
        end
      end else begin
        bit do_predict = 1'b1;
        case (csr_name)
          "cmd": begin
            // check that HMAC is configured correctly before starting
            invalid_cfg = (`gmv(ral.cfg.digest_size) == SHA2_None) |
                          ((`gmv(ral.cfg.key_length) == Key_None) & `gmv(ral.cfg.hmac_en)) |
                          ((`gmv(ral.cfg.digest_size) == SHA2_256) &
                           (`gmv(ral.cfg.key_length) == Key_1024) &
                            `gmv(ral.cfg.hmac_en));
            `uvm_info(`gfn, $sformatf("invalid config at starting: %1b", invalid_cfg), UVM_LOW)

            if (sha_en && (!(hmac_start && item.a_data[HashStart]) &&
                           !(hmac_continue && item.a_data[HashContinue]))) begin
              if (item.a_data[HashProcess] && (hmac_start || hmac_continue)) begin
                {hmac_process, hmac_start} = item.a_data[1:0];
                if (!invalid_cfg) begin
                  check_idle_o(1'b0);
                  // only predict a new digest if configuration is valid and HMAC was indeed started
                  // otherwise previous digest is retained in CSRs
                  predict_digest(msg_q);
                end else begin
                  check_idle_o(1'b1);
                end
              end else if (item.a_data[HashStart]) begin
                {hmac_process, hmac_start} = item.a_data[1:0];
                // Clear this variable when context has to be skipped as HASH continue won't be set
                if (cfg.sar_skip_ctxt) begin
                  hmac_stopped = 0;
                end
                if (invalid_cfg) begin
                  update_err_intr_code(SwInvalidConfig);
                end else begin
                  check_idle_o(1'b0);
                  update_wr_msg_length(0);
                  // update digest size to the new one at start/continue signal when valid context
                  if (!cfg.sar_skip_ctxt) begin
                    previous_digest_size = `gmv(ral.cfg.digest_size);
                  end
                  `uvm_info(`gfn, $sformatf(
                            "setting previous digest: %4b", previous_digest_size), UVM_HIGH)
                end
              end
            end else if (item.a_data[HashStart] || item.a_data[HashContinue]) begin
              if (!sha_en && !invalid_cfg) begin
                // so long as configuration is valid
                update_err_intr_code(SwHashStartWhenShaDisabled);
                // To cover when SHA is disabled
                if (cfg.en_cov) cov.cfg_cg.sample(`gmv(ral.cfg));
              end else if (invalid_cfg) begin
                // otherwise signalling invalid config takes priority
                update_err_intr_code(SwInvalidConfig);
              end else begin
                update_err_intr_code(SwHashStartWhenActive);
              end
            end
            // Detect when stop has been triggered to store the current state, for Save and Restore
            // check
            if (item.a_data[HashStop]) begin
              int block_size;
              int mult;
              int mod;
              int msg_slice_length;

              hmac_stopped = 1;

              // Retrieve block size (in bits) according to configured digest size
              block_size = get_block_size(`gmv(ral.cfg.digest_size));

              // Block size has to be not zero to avoid to divide by zero
              if (block_size != 0) begin
                // Round up message counter to the block boundary to predict message being processed
                // so far by the DUT.
                // hmac_rd_cnt is multiplied by 32 to express it in bits.
                // block_size is divided by 8 to express it in bytes.
                mult             = (hmac_rd_cnt * 32 + block_size - 1) / block_size;
                msg_slice_length = mult * block_size / 8;
              end else begin
                msg_slice_length = 0;
              end

              // In case the remaining message is less than a block size, push only this remaining
              // message into the queue.
              if (msg_slice_length > msg_q.size()) begin
                msg_slice_length = msg_q.size();
              end

              // Push partial message into a new queue to be processed by the digest predictor
              for (int i=0; i<msg_slice_length; i++) begin
                msg_part_q.push_back(msg_q[i]);
              end
              // Process digest only when configuration is valid, otherwise retain the previous
              if (!invalid_cfg) begin
                predict_digest(msg_part_q);
              end
            end
            if (item.a_data[HashContinue]) begin
              // update digest size to the new one at start/continue signal when valid context
              if (!cfg.sar_skip_ctxt) begin
                previous_digest_size = `gmv(ral.cfg.digest_size);
              end
              `uvm_info(`gfn, $sformatf(
                        "setting previous digest: %4b", previous_digest_size), UVM_HIGH)
              hmac_continue = 1;
              hmac_stopped  = 0;  // Clear this variable to be able to compare digest if needed
            end
          end
          "intr_test": begin // testmode, intr_state is W1C, cannot use UVM_PREDICT_WRITE
            intr_test = item.a_data;
            // As INTR_STATE.hmac_err and INTR_STATE.hmac_done are RW1C, we should get back the
            // current state
            intr_state_exp = intr_test | `gmv(ral.intr_state);
            void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
            if (cfg.en_cov) begin
              bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
              hmac_intr_e     intr;
              intr = intr.first;
              do begin
                cov.intr_test_cg.sample(intr, intr_test[intr], intr_en[intr],
                                        intr_state_exp[intr]);
                intr = intr.next;
              end while (intr != intr.first);
            end
          end
          "intr_state": begin
            // Do nothing
          end
          "cfg": begin
            if (hmac_start) begin
              if (cfg.en_cov) cov.wr_config_during_hash_cg.sample(1);
              return; // won't update configs if hash start
            end
            // Changing the key length should be seamless while HMAC disabled
            if (!item.a_data[HmacEn] && (item.a_data[KeyLengthMsb:KeyLengthLsb] !==
                                         `gmv(ral.cfg.key_length))) begin
              if (cfg.en_cov) cov.wr_key_during_sha_only_cg.sample(1);
            end
            if (sha_en && !item.a_data[ShaEn]) begin
              exp_digest   = '{default:0};  // Digest gets cleared on disabling.
              hmac_stopped = 0;             // Clear this to let digest comparison happening later
            end
            sha_en = item.a_data[ShaEn];
            // Sample CFG when SHA is enabled
            if (item.a_data[ShaEn]) begin
              if (cfg.en_cov) cov.cfg_cg.sample(item.a_data);
            end
          end
          "key_0", "key_1", "key_2", "key_3", "key_4", "key_5", "key_6", "key_7",
          "key_8", "key_9", "key_10", "key_11", "key_12", "key_13", "key_14", "key_15",
          "key_16", "key_17", "key_18", "key_19", "key_20", "key_21", "key_22", "key_23",
          "key_24", "key_25", "key_26", "key_27", "key_28", "key_29", "key_30", "key_31": begin
            int key_idx = get_key_index(csr_name);

            if (hmac_start) begin
              if (cfg.en_cov) cov.wr_key_during_hash_cg.sample(1);
              update_err_intr_code(SwUpdateSecretKeyInProcess);
              return;
            end

            key[key_idx] = item.a_data;
          end
          "wipe_secret": begin
            // TODO (#23563): when writing wipe_secret, trigger RTL assertion checks
          end
          "intr_enable", "intr_state", "alert_test", "status": begin
            // Do nothing
          end
          "digest_0", "digest_1", "digest_2", "digest_3", "digest_4", "digest_5", "digest_6",
          "digest_7", "digest_8", "digest_9", "digest_10", "digest_11", "digest_12", "digest_13",
          "digest_14", "digest_15", "msg_length_upper", "msg_length_lower": begin
            // Predict updated value coming from write iff SHA core is disabled.
            do_predict = !sha_en;
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        endcase
        if (do_predict) begin
          // csr write: predict and update according to the csr names
          void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
          if (csr_name.substr(0, 5) == "digest") begin
            // When predicting a new value of the DIGEST registers due to a write, also update
            // `exp_digest` with the prediction.
            int digest_idx = get_digest_index(csr_name);
            if (`gmv(ral.cfg.digest_swap)) begin
              exp_digest[digest_idx] = {<<8{`gmv(csr)}};
            end else begin
              exp_digest[digest_idx] = `gmv(csr);
            end
          end else if (csr_name == "cfg") begin
            // update prediction of digest_size to SHA2_None for all invalid inputs
            if ((item.a_data[DigestSizeMsb:DigestSizeLsb] != SHA2_256) &&
                (item.a_data[DigestSizeMsb:DigestSizeLsb] != SHA2_384) &&
                (item.a_data[DigestSizeMsb:DigestSizeLsb] != SHA2_512)) begin
              void'(ral.cfg.digest_size.predict(.value(SHA2_None), .kind(UVM_PREDICT_WRITE)));
            end

            // update prediction of key_length to Key_None for all invalid inputs
            if ((item.a_data[KeyLengthMsb:KeyLengthLsb] != Key_128) &&
                (item.a_data[KeyLengthMsb:KeyLengthLsb] != Key_256) &&
                (item.a_data[KeyLengthMsb:KeyLengthLsb] != Key_384) &&
                (item.a_data[KeyLengthMsb:KeyLengthLsb] != Key_512) &&
                (item.a_data[KeyLengthMsb:KeyLengthLsb] != Key_1024)) begin
              void'(ral.cfg.key_length.predict(.value(Key_None), .kind(UVM_PREDICT_WRITE)));
            end
          end
        end
      end
    end

    // predict status based on csr read addr channel
    if (!write && channel != DataChannel) begin
      // Update expected status register
      if (csr_name == "status") begin
        hmac_status_data = (hmac_idle       << HmacStaIdle)         |
                           (hmac_fifo_empty << HmacStaMsgFifoEmpty) |
                           (hmac_fifo_full  << HmacStaMsgFifoFull)  |
                           (hmac_fifo_depth << HmacStaMsgFifoDepthLsb);
        void'(ral.status.predict(.value(hmac_status_data), .kind(UVM_PREDICT_READ)));
      // Update expected FIFO Empty interrupt register
      end else if (csr_name == "intr_state") begin
        // Bitwise OR is needed to retrieve previous values as some fields are W1C
        bit intr_state_empty = fifo_empty_intr | intr_test[HmacMsgFifoEmpty];
        void'(ral.intr_state.fifo_empty.predict(.value(intr_state_empty), .kind(UVM_PREDICT_READ)));
      end
      return;
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write) begin
      case (csr_name)
        "intr_state": begin
          if (!do_cycle_accurate_check) begin
            do_read_check = 0;
          end
          if (cfg.en_cov) begin
            bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
            hmac_intr_e     intr;
            intr = intr.first;
            do begin
              cov.intr_cg.sample(intr, intr_en[intr], item.d_data[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
              intr = intr.next;
            end while (intr != intr.first);
          end
          if (item.d_data[HmacDone]) begin
            // here check DUT should only trigger hmac_done when sha is enabled, and
            // previously triggered hash_process or hash_stop.
            // future throughput test should check the accurate cycles
            if (sha_en && (hmac_process || hmac_stopped)) begin
              void'(ral.intr_state.hmac_done.predict(.value(1), .kind(UVM_PREDICT_READ)));
            end
            check_idle_o(1'b1);
            flush();
          end
          // hmac has been triggered and config is invalid
          if (hmac_start && invalid_cfg) begin
            flush();
          end
          // TODO(#23739): remove the lines below when RTL PR got merged
          // --- BEGIN ---
          fifo_empty = item.d_data[HmacMsgFifoEmpty];
          void'(ral.intr_state.fifo_empty.predict(.value(fifo_empty), .kind(UVM_PREDICT_READ)));
          // ---  END  ---
        end
        "digest_0", "digest_1", "digest_2", "digest_3", "digest_4", "digest_5", "digest_6",
        "digest_7", "digest_8", "digest_9", "digest_10", "digest_11", "digest_12", "digest_13",
        "digest_14", "digest_15": begin
          int digest_idx = get_digest_index(csr_name);
          // By default, the hardware outputs little-endian data for each digest (32 bits). But DPI
          // functions/test vectors from specs expect output to be big-endian.
          // Therefore we should flip the expected value if digest_swap is zero.
          bit [TL_DW-1:0] real_digest_val;

          // Read and check DIGEST while HMAC is enabled/disabled
          if (cfg.en_cov) cov.rd_digest_during_hmac_en_cg.sample(`gmv(ral.cfg.hmac_en));

          if (!`gmv(ral.cfg.digest_swap)) begin
            // digest_swap is set to true to match spec vectors/expected digest word (big-endian)
            // when digest swap is not true, then we need to swap the digest word
            // to be able to compare it with the expected digest word (big-endian)
            real_digest_val = {<<8{item.d_data}};
          end else begin
            real_digest_val = item.d_data;
          end

          // decide whether to assume previous or new digest size to compare correctly
          // with the expected digest, because digests are retained from previous operation
          // until new configuration is successfully started
          if (previous_digest_size != `gmv(ral.cfg.digest_size)) begin
            expected_digest_size = previous_digest_size;
          end else begin
            expected_digest_size = `gmv(ral.cfg.digest_size);
          end

          `uvm_info(`gfn, $sformatf(
                      "comparing digest sizes (previous, cfg, and expected): %4b, %4b, %4b",
                      previous_digest_size, `gmv(ral.cfg.digest_size),
                      expected_digest_size), UVM_HIGH)

          // Predict intermediate digest values when S&R has been triggered
          // TODO (#23240): modify the C model to be able to provide intermediate digest
          // if (hmac_stopped) predict_digest(msg_q);
          // And remove lines, when C model will support intermediate hash. For the moment don't
          // compare digest. Only the final digest will be compared in case of S&R, this is enough
          // for the moment
          // Proceed with read digest and compare values with expected
          if (!hmac_stopped) begin
            // If wipe_secret is triggered, ensure the predicted value does not match the read out
            // digest and update the predicted value with the read out value.
            if (cfg.wipe_secret_triggered) begin
              `DV_CHECK_NE(real_digest_val, exp_digest[digest_idx])
              `uvm_info(`gfn, $sformatf("updating digest to read value after wiping 0x%0h",
                        exp_digest[digest_idx]), UVM_HIGH)
              // update new digest data to the exp_digest variable.
              exp_digest[digest_idx] = real_digest_val;
            end else begin // !cfg.wipe_secret_triggered
              // only check till digest_idx = 7 for SHA-2 256 and till digest_idx = 11 for SHA-2 384
              // Remaining digest values are irrelevant or truncated for these digest sizes.
              if (((expected_digest_size == SHA2_256) && (digest_idx < 8))  ||
                  ((expected_digest_size == SHA2_384) && (digest_idx < 12)) ||
                    expected_digest_size == SHA2_512) begin
                `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx])
              end
            end
          end
          return;
        end
        "status": begin
          if (!do_cycle_accurate_check || cfg.sar_skip_ctxt) begin
            do_read_check = 0;
          end
          if (cfg.en_cov) cov.status_cg.sample(item.d_data, `gmv(ral.cfg));
          // TODO (issue #23380): Verify idle status now exposed to SW
          hmac_idle = item.d_data[HmacStaIdle];
          void'(ral.status.hmac_idle.predict(.value(hmac_idle), .kind(UVM_PREDICT_READ)));
        end
        "msg_length_lower": begin
          if (cfg.sar_skip_ctxt) begin
            do_read_check = 0;
          end
          if (cfg.en_cov) begin
            cov.msg_len_cg.sample(.msg_len_lower(item.d_data),
                                  .msg_len_upper('x),
                                  .cfg(`gmv(ral.cfg)));
          end
        end
        "msg_length_upper": begin
          if (cfg.sar_skip_ctxt) begin
            do_read_check = 0;
          end
          if (cfg.en_cov) begin
            cov.msg_len_cg.sample(.msg_len_lower('x),
                                  .msg_len_upper(item.d_data),
                                  .cfg(`gmv(ral.cfg)));
          end
        end
        "err_code": if (cfg.en_cov) cov.err_code_cg.sample(item.d_data);
        "key_0", "key_1", "key_2", "key_3", "key_4", "key_5", "key_6", "key_7", "key_8", "key_9",
        "key_10", "key_11", "key_12", "key_13", "key_14", "key_15", "key_16", "key_17", "key_18",
        "key_19", "key_20", "key_21", "key_22", "key_23", "key_24", "key_25", "key_26", "key_27",
        "key_28", "key_29", "key_30", "key_31", "cfg", "cmd", "intr_enable", "intr_test",
        "wipe_secret", "alert_test": begin
          // Do nothing
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
      if (do_read_check) begin
        `uvm_info(`gfn, $sformatf("%s reg is checked with expected value %0h",
                                  csr_name, `gmv(csr)), UVM_HIGH)
        `DV_CHECK_EQ(item.d_data, `gmv(csr), csr_name)
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask : process_tl_access

  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    if (cfg.en_cov) cov.trig_rst_during_hash_cg.sample(hmac_process);

    // Should be reinitialized before flushing as it will be used as a condition
    hmac_stopped = 0;
    flush();
    key             = '{default:0};
    exp_digest      = '{default:0};
    hmac_idle       = ral.status.hmac_idle.get_reset();
    hmac_fifo_empty = ral.status.fifo_empty.get_reset();
    hmac_fifo_full  = ral.status.fifo_full.get_reset();
    hmac_fifo_depth = ral.status.fifo_depth.get_reset();
    hmac_start      = ral.cmd.hash_start.get_reset();
    sha_en          = ral.cfg.sha_en.get_reset();
    hmac_stopped    = 0;
    msg_q.delete();
    msg_part_q.delete();
    cfg.wipe_secret_triggered = 0;
  endfunction : reset

  // clear variables after hmac_done
  virtual function void flush();
    // Do not flush counters if the current context should be ignored or if stopped
    if (!hmac_stopped && !cfg.sar_skip_ctxt) begin
      hmac_wr_cnt  = 0;
      hmac_rd_cnt  = 0;
      msg_q.delete();
    end
    hmac_process        = 0;
    hmac_start          = 0;
    hmac_continue       = 0;
    hmac_process_last   = 0;
    hmac_start_last     = 0;
    hmac_stopped_last   = 0;
    hmac_continue_last  = 0;
    fifo_full_detected  = 0;
    fifo_empty_intr     = 0;
    void'(ral.intr_state.fifo_empty.predict(.value(fifo_empty_intr | intr_test[HmacMsgFifoEmpty]),
                                            .kind(UVM_PREDICT_READ)));
  endfunction : flush

  // hmac_wr_cnt was incremented every time when msg_q has 4 bytes streamed in
  // or when hash_process is triggered, and there are some remaining bytes
  // this task will also clear the msg_q queue once hmac_process is set
  virtual task hmac_process_fifo_wr();
    bit has_unprocessed_msg;
    forever begin
      has_unprocessed_msg = 1;
      wait(msg_q.size() >= (hmac_wr_cnt + 1) * 4 || (hmac_process && msg_q.size() > 0));
      // Ensure that current context has to be taken into account or skipped
      if (cfg.sar_skip_ctxt) begin
        wait(!cfg.sar_skip_ctxt);
      end
      // if hmac process is issued and there are still unprocessed word (can hold up to at
      // most one word), then the hmac_wr_cnt will increment
      // if all the written msgs have been process, will skip the counter incrementation
      if (hmac_process) begin
        if (msg_q.size() <= hmac_wr_cnt * 4) begin
          has_unprocessed_msg = 0;
        end
        msg_q.delete();
        msg_part_q.delete();
      end
      if (sha_en && has_unprocessed_msg) begin
        // if fifo full, tlul will not write next data until fifo has space again
        if ((hmac_wr_cnt - hmac_rd_cnt) == HMAC_MSG_FIFO_DEPTH_WR) begin
          wait((hmac_wr_cnt - hmac_rd_cnt) < HMAC_MSG_FIFO_DEPTH_WR);
        end
        @(negedge cfg.clk_rst_vif.clk);
        if (!hmac_stopped) begin
          hmac_wr_cnt++;
          `uvm_info(`gfn, $sformatf("increase wr cnt %0d", hmac_wr_cnt), UVM_HIGH)
          cfg.clk_rst_vif.wait_clks(HMAC_WR_WORD_CYCLE);
        end
      end
    end
  endtask : hmac_process_fifo_wr

  virtual task hmac_process_fifo_status();
    bit pre_fifo_empty_intr;
    forever @(hmac_wr_cnt, hmac_rd_cnt, hmac_process, hmac_start, hmac_stopped, hmac_continue) begin
      // Store hmac_process and hmac_start to be able to detect when it goes up, as it could remain
      // up for a while
      bit hmac_process_posedge  = hmac_process & ~hmac_process_last;
      bit hmac_start_posedge    = hmac_start & ~hmac_start_last;
      bit hmac_stopped_posedge  = hmac_stopped & ~hmac_stopped_last;
      bit hmac_continue_posedge = hmac_continue & ~hmac_continue_last;

      // Store last value to be able to detect signal change
      hmac_process_last  = hmac_process;
      hmac_stopped_last  = hmac_stopped;
      hmac_start_last    = hmac_start;
      hmac_continue_last = hmac_continue;

      // when hmac_wr_cnt and hmac_rd_cnt update at the same time, wait the clock rising edge
      // to guarantee get both update and at the same time as the DUT
      cfg.clk_rst_vif.wait_clks(1);

      // Compute FIFO level flags
      hmac_fifo_depth = hmac_wr_cnt - hmac_rd_cnt;
      hmac_fifo_full  = hmac_fifo_depth == HMAC_MSG_FIFO_DEPTH_WR;
      hmac_fifo_empty = hmac_fifo_depth == 0;

      // The FIFO empty interrupt is raised only if the message FIFO is actually writable by
      // software, i.e., if all of the following conditions are met:
      //   1- The HMAC block is not running in HMAC mode and performing the second round of
      //      computing the final hash of the outer key as well as the result of the first round
      //      using the inner key.
      //   2- Software has not yet written the Process or Stop command to finish the hashing
      //      operation.
      //   3- The message FIFO must also have been full previously. Otherwise, the hardware empties
      //      the FIFO faster than software can fill it and there is no point in interrupting the
      //      software to inform it about the message FIFO being empty.
      if (fifo_full_detected && hmac_fifo_empty) begin
        pre_fifo_empty_intr = 1;
      end else begin
        pre_fifo_empty_intr = 0;
      end

      // Delay FIFO empty signal to be aligned with the DUT behavior
      fork
        begin
          cfg.clk_rst_vif.wait_clks(1);
          fifo_empty_intr = pre_fifo_empty_intr;
        end
      join_none

      // Check whether FIFO full has been detected for the ongoing message but the retrictions cases
      // have the priority in case full is set at the same moment
      if (hmac_fifo_empty || hmac_start_posedge || hmac_process_posedge ||
          hmac_stopped_posedge || hmac_continue_posedge) begin
        fifo_full_detected = 0;
      end else if (hmac_fifo_full) begin
        fifo_full_detected = 1;
      end
    end
  endtask : hmac_process_fifo_status

  // Spawn process to check interrupt pins in test mode
  virtual task hmac_intr_test();
    foreach (intr_test[intr_i]) begin
      fork begin
        hmac_intr_test_pin(intr_i);
      end join_none
    end
  endtask : hmac_intr_test

  // Check interrupt pins in test mode
  virtual task hmac_intr_test_pin(int intr_i);
    bit [TL_DW-1:0] intr_en;
    hmac_intr_e     intr = hmac_intr_e'(intr_i);
    forever @(intr_test[intr_i]) begin
      intr_en = `gmv(ral.intr_enable);
      if (intr_test[intr_i]) begin
        // Check interrupt state pins only if enabled
        if (intr_en[intr_i]) begin
          fork: intr_pins
            begin
              wait(cfg.intr_vif.pins[intr_i]);
              `uvm_info(`gfn, $sformatf("Detected interrupt on pin %s", intr.name()), UVM_HIGH)
            end
            begin
              cfg.clk_rst_vif.wait_clks(100); // 100 clk cycles timeout
              `uvm_error(`gfn, $sformatf("Wait pin interrupt timeout for %s", intr.name()))
            end
          join_any
          disable fork;
        end
      end
    end
  endtask : hmac_intr_test_pin

  // internal msg_fifo model to check fifo status and interrupt.
  // monitor rd_cnt and wr_cnt on the negedge of the clk
  // rd_cnt followed by wr_cnt with a clk cycle delay, except:
  // 1). hmac process key: DUT will process the key first
  // 2). read cnt reaches FIFO_MAX: DUT will process msg in the FIFO
  virtual task hmac_process_fifo_rd();
    bit key_processed = 0;
    fork
      begin : process_hmac_key_pad
        forever begin
          cfg.clk_rst_vif.wait_clks(1);
          // Key padding
          wait(hmac_start && sha_en);
          if (`gmv(ral.cfg.hmac_en) && hmac_rd_cnt == 0 && !invalid_cfg) begin
            if (`gmv(ral.cfg.digest_size) == SHA2_256) begin
              key_process_cycles = HMAC_KEY_PROCESS_CYCLES_256;
            end else begin
              key_process_cycles = HMAC_KEY_PROCESS_CYCLES_512;
            end
            // key_process_cycles for hmac key padding + 1 cycle for hash_start reg to reset
            cfg.clk_rst_vif.wait_clks(key_process_cycles + 1);
            @(negedge cfg.clk_rst_vif.clk);
            key_processed = 1;
          end
          while (1) begin
            // TODO: check if we need the error checking here - might not be necessary
            // break if hmac is done or if invalid config error is triggered or if SHA is
            // being disabled as HMAC enable configuration could be changed and thus
            // key_process_cycles might need to be updated
            if (`gmv(ral.intr_state.hmac_done) ||
                (`gmv(ral.intr_state.hmac_err) && `gmv(ral.err_code) == SwInvalidConfig) ||
                !sha_en) begin
              break;
            end
            cfg.clk_rst_vif.wait_clks(1);
          end
          key_processed = 0;
        end
      end

      begin : process_internal_fifo_rd
        forever begin
          // Ensure that current context has to be taken into account or skipped
          if (cfg.sar_skip_ctxt) begin
            wait(!cfg.sar_skip_ctxt);
          end
          wait((hmac_wr_cnt > hmac_rd_cnt) && (sha_en));
          if (`gmv(ral.cfg.hmac_en) && hmac_rd_cnt == 0) begin
            `uvm_info(`gfn, $sformatf("waiting on key processing to complete"), UVM_HIGH)
            wait(key_processed);
            `uvm_info(`gfn, $sformatf("key processing has completed"), UVM_HIGH)
          end
          #1ps; // delay 1 ps to make sure did not sample right at negedge clk
          cfg.clk_rst_vif.wait_n_clks(1);
          hmac_rd_cnt++;
          `uvm_info(`gfn, $sformatf("increase rd cnt %0d", hmac_rd_cnt), UVM_HIGH)
          // select correct FIFO read depth and message processing cycles
          if (`gmv(ral.cfg.digest_size) == SHA2_256) begin
            fifo_rd_depth        = HMAC_MSG_FIFO_DEPTH_RD_256;
            block_process_cycles = HMAC_MSG_PROCESS_CYCLES_256;
          end else begin
            fifo_rd_depth        = HMAC_MSG_FIFO_DEPTH_RD_512;
            block_process_cycles = HMAC_MSG_PROCESS_CYCLES_512;
          end
          if (hmac_rd_cnt % fifo_rd_depth == 0) begin
            `uvm_info(`gfn, $sformatf("start waiting on message processing now"), UVM_HIGH)
            cfg.clk_rst_vif.wait_n_clks(block_process_cycles);
            `uvm_info(`gfn, $sformatf("message processing has completed"), UVM_HIGH)
          end
        end
      end
    join_none
  endtask : hmac_process_fifo_rd

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacMsgFifoEmpty], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacDone], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacErr], 1'b0)
  endfunction : check_phase

  // query the sha / hmac c model to get expected digest
  // update predicted digest to ral mirrored value
  virtual function void predict_digest(
    bit [7:0] msg_i[],
    bit       sha_en      = `gmv(ral.cfg.sha_en),
    bit       hmac_en     = `gmv(ral.cfg.hmac_en),
    bit [3:0] digest_size = `gmv(ral.cfg.digest_size),
    bit [5:0] key_length  = `gmv(ral.cfg.key_length));
    bit [7:0] msg_tmp[];
    exp_digest = '{default:0}; // clear previous expected digest

    `uvm_info(`gfn, $sformatf("Computing digest prediction"), UVM_LOW)

    // TODO: predict even if sha_en == 0?
    case ({hmac_en, sha_en})
      2'b11: begin
        if (digest_size == SHA2_256) begin
          if (key_length == Key_128) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:3], msg_i, exp_digest[0:7]);
          end else if (key_length == Key_256) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:7], msg_i, exp_digest[0:7]);
          end else if (key_length == Key_384) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:11], msg_i, exp_digest[0:7]);
          end else if (key_length == Key_512) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:15], msg_i, exp_digest[0:7]);
          end else if (key_length == Key_1024) begin
            // model how the HW will limit key length to max of block size
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:15], msg_i, exp_digest[0:7]);
          end
        end else if (digest_size == SHA2_384) begin
          if (key_length == Key_128) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:3], msg_i, exp_digest[0:11]);
          if (key_length == Key_256) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:7], msg_i, exp_digest[0:11]);
          if (key_length == Key_384) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:11], msg_i, exp_digest[0:11]);
          if (key_length == Key_512) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:15], msg_i, exp_digest[0:11]);
          if (key_length == Key_1024) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:31], msg_i, exp_digest[0:11]);
        end else if (digest_size == SHA2_512) begin
          if (key_length == Key_128) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:3], msg_i, exp_digest);
          if (key_length == Key_256) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:7], msg_i, exp_digest);
          if (key_length == Key_384) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:11], msg_i, exp_digest);
          if (key_length == Key_512) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:15], msg_i, exp_digest);
          if (key_length == Key_1024) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:31], msg_i, exp_digest);
        end
        `uvm_info(`gfn, $sformatf("HMAC of key=%p, msg_i=%p: %p", key, msg_i, exp_digest), UVM_LOW)
      end
      2'b01: begin
        if (digest_size == SHA2_256) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha256_digest(msg_i, exp_digest[0:7]);
        end else if (digest_size == SHA2_384) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha384_digest(msg_i, exp_digest[0:11]);
        end else if (digest_size == SHA2_512) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha512_digest(msg_i, exp_digest);
        end
        `uvm_info(`gfn, $sformatf("SHA-2 digest of msg_i=%p: %p", msg_i, exp_digest), UVM_LOW)
      end
      default: begin
        // disgest is cleared if sha_en = 0
        exp_digest = '{default:0};
      end
    endcase
  endfunction : predict_digest

  virtual function void update_wr_msg_length(int size_bytes);
    uint64 size_bits = size_bytes * 8;
    void'(ral.msg_length_upper.predict(size_bits[TL_DW*2-1:TL_DW]));
    void'(ral.msg_length_lower.predict(size_bits[TL_DW-1:0]));
  endfunction : update_wr_msg_length

  virtual task update_err_intr_code(err_code_e err_code_val);
    if (!`gmv(ral.intr_state.hmac_err)) begin
      while (ral.intr_state.is_busy()) begin
        // using cfg.clk_rst_vif.wait_clks(1) instead was still resulting in race conditions with
        // the incrementing of hmac_rd_cnt and hmac_wr_cnt and a desynchronization
        #1ps;
      end
      void'(ral.intr_state.hmac_err.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));

      while (ral.err_code.is_busy()) begin
        // using cfg.clk_rst_vif.wait_clks(1) instead was still resulting in race conditions with
        // the incrementing of hmac_rd_cnt and hmac_wr_cnt and a desynchronization
        #1ps;
      end
      void'(ral.err_code.predict(.value(err_code_val), .kind(UVM_PREDICT_DIRECT)));
    end
  endtask : update_err_intr_code

  virtual function void check_idle_o(bit val);
    if (cfg.under_reset == 0) `DV_CHECK_EQ(cfg.hmac_vif.is_idle(), val)
  endfunction : check_idle_o

  virtual task monitor_cov();
    save_and_restore_e  sar_ctxt;
    uvm_event           sar_same_ctxt_ev;
    uvm_event           sar_different_ctxt_ev;
    uvm_event           sar_stop_continue_ev;
    sar_same_ctxt_ev      = uvm_event_sar_pool::get_global("sar_same_context_event");
    sar_different_ctxt_ev = uvm_event_sar_pool::get_global("sar_different_context_event");
    sar_stop_continue_ev  = uvm_event_sar_pool::get_global("sar_stop_and_continue_event");

    fork
      // Save and Restore with same context
      begin
        forever begin
          sar_same_ctxt_ev.wait_trigger();
          if (cfg.en_cov) cov.save_and_restore_cg.sample(.sar_ctxt(SameContext),
                                                         .cfg(`gmv(ral.cfg)));
        end
      end
      // Save and Restore with different contexts
      begin
        forever begin
          sar_different_ctxt_ev.wait_trigger();
          if (cfg.en_cov) cov.save_and_restore_cg.sample(.sar_ctxt(DifferentContext),
                                                         .cfg(`gmv(ral.cfg)));
        end
      end
      // Stop and Continue without Saving and Restoring
      begin
        forever begin
          sar_stop_continue_ev.wait_trigger();
          if (cfg.en_cov) cov.save_and_restore_cg.sample(.sar_ctxt(StopAndContinue),
                                                         .cfg(`gmv(ral.cfg)));
        end
      end
    join_none
  endtask : monitor_cov
endclass : hmac_scoreboard
