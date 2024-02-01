// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_scoreboard extends cip_base_scoreboard #(.CFG_T (hmac_env_cfg),
                                                    .RAL_T (hmac_reg_block),
                                                    .COV_T (hmac_env_cov));
  `uvm_component_utils(hmac_scoreboard)
  `uvm_component_new

  bit             sha_en, fifo_empty;
  bit [7:0]       msg_q[$];
  bit             hmac_start, hmac_process;
  int             hmac_wr_cnt, hmac_rd_cnt;
  bit [TL_DW-1:0] key[NUM_KEYS];
  bit [TL_DW-1:0] exp_digest[NUM_DIGESTS];
  bit [3:0]       digest_size, previous_digest_size, expected_digest_size;
  bit             previous_digest_swap, expected_digest_swap;
  bit [5:0]       key_length;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      hmac_process_fifo_status();
      hmac_process_fifo_wr();
      hmac_process_fifo_rd();
    join_none
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check           = 1'b1;
    bit     do_cycle_accurate_check = 1'b1;
    bit     write                   = item.is_write();
    string  csr_name;

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
        if (!hmac_start) begin
          update_err_intr_code(SwPushMsgWhenIdle);
        end else if (!sha_en) begin
          update_err_intr_code(SwPushMsgWhenShaDisabled);
        end else if (hmac_start && !cfg.under_reset) begin
          bit [7:0] bytes[4];
          bit [7:0] msg[$];
          {<<byte{bytes}} = item.a_data;
          // do endian swap in the word according to the mask, then push to the msg queue
          foreach (item.a_mask[i]) begin
            if (item.a_mask[i]) begin
              // endian_swap bit 1 operates at big endian data
              msg = (ral.cfg.endian_swap.get_mirrored_value()) ? {msg, bytes[i]} : {bytes[i], msg};
            end
          end
          foreach (msg[i]) msg_q.push_back(msg[i]);
          update_wr_msg_length(msg_q.size());
        end
      end else begin
        bit do_predict = 1'b1;
        case (csr_name)
          "cmd": begin
            if (sha_en && !(hmac_start && item.a_data[HashStart])) begin
              if (item.a_data[HashProcess] && hmac_start) begin
                {hmac_process, hmac_start} = item.a_data[1:0];
                predict_digest(msg_q);
                check_idle_o(1'b0);
              end else if (item.a_data[HashStart]) begin
                {hmac_process, hmac_start} = item.a_data[1:0];
                check_idle_o(1'b0);
                msg_q.delete(); // make sure next transaction won't include this msg_q
                update_wr_msg_length(0);
                // update digest size and swap to the new one only at the start signal
                previous_digest_size = ral.cfg.digest_size.get_mirrored_value();
                previous_digest_swap = ral.cfg.digest_swap.get_mirrored_value();

                `uvm_info(`gfn, $sformatf(
                          "Setting previous digest and digest swap: %4b",
                           previous_digest_size), UVM_HIGH)

              end
            end else if (item.a_data[HashStart] == 1) begin
              if (!sha_en) begin
                update_err_intr_code(SwHashStartWhenShaDisabled);
              end else begin
                update_err_intr_code(SwHashStartWhenActive);
              end
            end
          end
          "intr_test": begin // testmode, intr_state is W1C, cannot use UVM_PREDICT_WRITE
            bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
            void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
            if (cfg.en_cov) begin
              bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
              hmac_intr_e     intr;
              intr = intr.first;
              do begin
                cov.intr_test_cg.sample(intr, item.a_data[intr], intr_en[intr],
                                        intr_state_exp[intr]);
                intr = intr.next;
              end while (intr != intr.first);
            end
          end
          "intr_state": begin
            // Do nothing
          end
          "cfg": begin
            if (hmac_start) return; // won't update configs if hash start
            if (cfg.en_cov) cov.cfg_cg.sample(item.a_data);
            if (sha_en && !item.a_data[ShaEn]) begin
              // Digest gets cleared on disabling.
              exp_digest = {default: '0};
            end
            sha_en = item.a_data[ShaEn];
          end
          "key_0", "key_1", "key_2", "key_3", "key_4", "key_5", "key_6", "key_7",
          "key_8", "key_9", "key_10", "key_11", "key_12", "key_13", "key_14", "key_15",
          "key_16", "key_17", "key_18", "key_19", "key_20", "key_21", "key_22", "key_23",
          "key_24", "key_25", "key_26", "key_27", "key_28", "key_29", "key_30", "key_31": begin
            int key_idx = get_key_index(csr_name);

            if (hmac_start) begin
              update_err_intr_code(SwUpdateSecretKeyInProcess);
              return;
            end

            key[key_idx] = item.a_data;
          end
          "wipe_secret", "intr_enable", "intr_state", "alert_test": begin
            // Do nothing
          end
          "digest_7", "digest_8", "digest_9", "digest_10", "digest_11", "digest_12", "digest_13",
          "digest_14", "digest_15", "status", "msg_length_upper", "msg_length_lower": begin
            // Predict updated value coming from write iff SHA core is disabled.
            do_predict = !sha_en;
          end
          "status": begin
            `uvm_error(`gfn, $sformatf("this reg does not have write access: %0s",
                                       csr.get_full_name()))
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
            if (ral.cfg.digest_swap.get_mirrored_value() == 1'b1) begin
              exp_digest[digest_idx] = {<<8{`gmv(csr)}};
            end else begin
              exp_digest[digest_idx] = `gmv(csr);
            end
          end
        end
      end
    end

    // predict status based on csr read addr channel
    if (!write && channel != DataChannel) begin
        if (csr_name == "status") begin
          bit [5:0]       hmac_fifo_depth  = hmac_wr_cnt - hmac_rd_cnt;
          bit             hmac_fifo_full   = hmac_fifo_depth == HMAC_MSG_FIFO_DEPTH;
          bit             hmac_fifo_empty  = hmac_fifo_depth == 0;
          bit [TL_DW-1:0] hmac_status_data = (hmac_fifo_empty << HmacStaMsgFifoEmpty) |
                                             (hmac_fifo_full  << HmacStaMsgFifoFull) |
                                             (hmac_fifo_depth << HmacStaMsgFifoDepth);
          void'(ral.status.predict(.value(hmac_status_data), .kind(UVM_PREDICT_READ)));
        end else if (csr_name == "intr_state") begin
          if (fifo_empty && ral.intr_state.fifo_empty.get_mirrored_value() != 1) begin
            void'(ral.intr_state.fifo_empty.predict(.value(1), .kind(UVM_PREDICT_READ)));
          end
        end
      return;
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write) begin
      case (csr_name)
        "intr_state": begin
          if (!do_cycle_accurate_check) do_read_check = 0;
          if (cfg.en_cov) begin
            bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
            hmac_intr_e     intr;
            intr = intr.first;
            do begin
              cov.intr_cg.sample(intr, intr_en[intr], item.d_data[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
              intr = intr.next;
            end while (intr != intr.first);
          end
          if (item.d_data[HmacDone] == 1) begin
            // here check DUT should only trigger hmac_done when sha is enabled, and
            // previously triggered hash_process.
            // future throughput test should check the accurate cycles
            if (sha_en && hmac_process) begin
              void'(ral.intr_state.hmac_done.predict(.value(1), .kind(UVM_PREDICT_READ)));
            end
            check_idle_o(1'b1);
            flush();
          end
          // TODO(#21815): Verify FIFO empty status interrupt.
          fifo_empty = item.d_data[HmacMsgFifoEmpty];
          void'(ral.intr_state.fifo_empty.predict(.value(fifo_empty), .kind(UVM_PREDICT_READ)));
        end
        "digest_0", "digest_1", "digest_2", "digest_3", "digest_4", "digest_5", "digest_6",
        "digest_7", "digest_8", "digest_9", "digest_10", "digest_11", "digest_12", "digest_13",
        "digest_14", "digest_15": begin
          int digest_idx = get_digest_index(csr_name);
          // By default, the hardware outputs little-endian data for each digest (32 bits). But DPI
          // functions expect output to be big-endian. Thus we should flip the expected value if
          // digest_swap is zero.
          bit [TL_DW-1:0] real_digest_val;

          // TODO: will need this chunk of code if we decide to hold the previous digest
          // value after HMAC is configured with new size etc. when doing DV for
          // the new digest sizes

          /* if (previous_digest_swap != ral.cfg.digest_swap.get_mirrored_value()) begin
              expected_digest_swap = previous_digest_swap;
          end else begin
              expected_digest_swap = ral.cfg.digest_swap.get_mirrored_value();
          end */

          // when testing only 256-bit now, digest output is wired directly
          // to registers and swaps are directly reflected in the CSRs
          // so do not need to hold previous digest swap cfg
          expected_digest_swap = ral.cfg.digest_swap.get_mirrored_value();

          if (expected_digest_swap == 1'b0) begin
            // this only swaps the 32-bit word, but not the full 64-bit digest word for the
            // extended modes, have to swap checks at the bottom
            real_digest_val = {<<8{item.d_data}};
          end else begin
            real_digest_val = item.d_data;
          end

          // decide whether to assume previous or new digest size to compare correctly
          // with the expected digest
          if (previous_digest_size != ral.cfg.digest_size.get_mirrored_value()) begin
              expected_digest_size = previous_digest_size;
          end else begin
              expected_digest_size = ral.cfg.digest_size.get_mirrored_value();
          end

          `uvm_info(`gfn, $sformatf(
                      "Comparing digest (previous, cfg, and expected): %4b, %4b, %4b",
                       previous_digest_size, ral.cfg.digest_size.get_mirrored_value(),
                       expected_digest_size), UVM_HIGH)

          // If wipe_secret is triggered, ensure the predicted value does not match the readout
          // digest.
          if (cfg.wipe_secret_triggered) begin
            if (expected_digest_size == SHA2_256) begin
              if (digest_idx < 8) begin
                `DV_CHECK_NE(real_digest_val, exp_digest[digest_idx]);
                // Update new digest data to the exp_digest variable.
                 exp_digest[digest_idx] = real_digest_val;
                `uvm_info(`gfn, $sformatf("Updating digest to read value after wiping 0x%0h",
                          exp_digest[digest_idx]), UVM_HIGH)
              end
            end
          end else begin
            `uvm_info(`gfn, $sformatf("expected digest[%0d] 0x%0h",
                      digest_idx, exp_digest[digest_idx]), UVM_LOW)
            if (expected_digest_size == SHA2_256) begin
              if (digest_idx < 8) begin
                `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx]);
              end else begin
                `DV_CHECK_EQ(real_digest_val, '0);
              end
            end else if (expected_digest_size == SHA2_512) begin
                if (expected_digest_swap == 1'b0) begin
                   if (digest_idx % 2) begin // odd index then compare with smaller index
                    `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx-1]);
                   end else begin
                    `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx+1]);
                   end
                end else begin
                  `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx]);
                end
            end else if (expected_digest_size == SHA2_384) begin
              if (digest_idx > 11) begin
                `DV_CHECK_EQ(real_digest_val, '0); // truncated digest words
              end else begin
                if (expected_digest_swap == 1'b0) begin
                   if (digest_idx % 2) begin // odd index then compare with smaller index
                    `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx-1]);
                   end else begin
                    `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx+1]);
                   end
                end else begin
                  `DV_CHECK_EQ(real_digest_val, exp_digest[digest_idx]);
                end
              end
            end
          end
          return;
        end
        "status": begin
          if (!do_cycle_accurate_check) do_read_check = 0;
          if (cfg.en_cov) cov.status_cg.sample(item.d_data, ral.cfg.get_mirrored_value());
        end
        "msg_length_upper": begin
          if (cfg.en_cov) begin
            cov.msg_len_cg.sample(item.d_data, ral.cfg.get_mirrored_value());
          end
        end
        "err_code": if (cfg.en_cov) cov.err_code_cg.sample(item.d_data);
        "key_0", "key_1", "key_2", "key_3", "key_4", "key_5", "key_6", "key_7", "key_8", "key_9",
        "key_10", "key_11", "key_12", "key_13", "key_14", "key_15", "key_16", "key_17", "key_18",
        "key_19", "key_20", "key_21", "key_22", "key_23", "key_24", "key_25", "key_26", "key_27",
        "key_28", "key_29", "key_30", "key_31", "cfg", "cmd", "intr_enable", "intr_test",
        "wipe_secret", "msg_length_lower", "alert_test": begin
          // Do nothing
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
      // TODO: uncomment this. It errors out on the FIFO status.
      //if (do_read_check) begin
      //  `uvm_info(`gfn, $sformatf("%s reg is checked with expected value %0h",
      //                            csr_name, csr.get_mirrored_value()), UVM_LOW)
      //  `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, csr_name)
      // end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    flush();
    sha_en     = 0;
    fifo_empty = 0;
    hmac_start = 0;

    key             = '{default:0};
    key_length      = 5'b0_0001;
    digest_size     = 4'b0001;
    exp_digest      = '{default:0};
    msg_q.delete();
    cfg.wipe_secret_triggered = 0;
  endfunction

  // clear variables after hmac_done
  virtual function void flush();
    hmac_wr_cnt  = 0;
    hmac_rd_cnt  = 0;
    hmac_process = 0;
  endfunction

  // hmac_wr_cnt was incremented every time when msg_q has 4 bytes streamed in
  // or when hash_process is triggered, and there are some remaining bytes
  // this task will also clear the msg_q queue once hmac_process is set
  virtual task hmac_process_fifo_wr();
    fork
      begin : insolation_fork_process_fifo_wr
        forever begin
          wait(!cfg.under_reset);
          fork
            begin : increase_wr_cnt
              bit has_unprocessed_msg = 1;
              wait(msg_q.size() >= (hmac_wr_cnt + 1) * 4 || (hmac_process && msg_q.size() > 0));
              // if hmac process is issued and there are still unprocessed word (can hold up to at
              // most one word), then the hmac_wr_cnt will increment
              // if all the written msgs have been process, will skip the counter incrementation
              if (hmac_process) begin
                if (msg_q.size() <= hmac_wr_cnt * 4) has_unprocessed_msg = 0;
                msg_q.delete();
              end
              if (sha_en && has_unprocessed_msg) begin
                // if fifo full, tlul will not write next data until fifo has space again
                if ((hmac_wr_cnt - hmac_rd_cnt) == HMAC_MSG_FIFO_DEPTH) begin
                  wait((hmac_wr_cnt - hmac_rd_cnt) < HMAC_MSG_FIFO_DEPTH);
                end
                @(negedge cfg.clk_rst_vif.clk);
                hmac_wr_cnt++;
                `uvm_info(`gfn, $sformatf("increase wr cnt %0d", hmac_wr_cnt), UVM_HIGH)
                cfg.clk_rst_vif.wait_clks(HMAC_WR_WORD_CYCLE);
              end
            end
            begin : reset_increase_wr_cnt
              wait(cfg.under_reset);
            end
          join_any
          disable fork;
        end // end forever
      end
    join
  endtask

  virtual task hmac_process_fifo_status();
    forever @(hmac_wr_cnt, hmac_rd_cnt) begin
      // when hmac_wr_cnt and hmac_rd_cnt update at the same time, wait 1ps to guarantee
      // get both update
      #1ps;
      if ((hmac_wr_cnt == hmac_rd_cnt) && (hmac_wr_cnt != 0)) begin
        // after the rd wr pointers are equal, wait one clk cycle for the fifo_empty register
        // update, wait another clk cycle for the register value to reflect
        if (!fifo_empty) begin
          cfg.clk_rst_vif.wait_clks(2);
          `uvm_info(`gfn, "predict interrupt fifo empty is set", UVM_HIGH)
          fifo_empty = 1;
        end
      end
    end
  endtask

  // internal msg_fifo model to check fifo status and interrupt.
  // monitor rd_cnt and wr_cnt on the negedge of the clk
  // rd_cnt followed by wr_cnt with a clk cycle delay, except:
  // 1). hmac process key: DUT will process the key first
  // 2). read cnt reaches FIFO_MAX: DUT will process msg in the FIFO
  virtual task hmac_process_fifo_rd();
    bit key_processed;
    fork
      begin : process_hmac_key_pad
        forever begin
          wait(!cfg.under_reset);
          // delay 1ps to make sure all variables are being reset, before moving to the next
          // forever loop
          #1ps;
          fork
            begin : key_padding
              wait(hmac_start && sha_en);
              if (ral.cfg.hmac_en.get_mirrored_value() && hmac_rd_cnt == 0) begin
                // 80 cycles for hmac key padding, 1 cycle for hash_start reg to reset
                cfg.clk_rst_vif.wait_clks(HMAC_KEY_PROCESS_CYCLES + 1);
                @(negedge cfg.clk_rst_vif.clk);
                key_processed = 1;
              end
              while (1) begin
                if (ral.intr_state.hmac_done.get_mirrored_value() == 1) break;
                cfg.clk_rst_vif.wait_clks(1);
              end
            end
            begin : reset_key_padding
              wait(cfg.under_reset);
            end
          join_any
          disable fork;
          key_processed = 0;
        end // end forever
      end

      begin : process_internal_fifo_rd
        forever begin
          wait(!cfg.under_reset);
          // delay 1ps to make sure all variables are being reset, before moving to the next
          // forever loop
          #1ps;
          fork
            begin : hmac_fifo_rd
              wait((hmac_wr_cnt > hmac_rd_cnt) && (sha_en));
              if (ral.cfg.hmac_en.get_mirrored_value() && hmac_rd_cnt == 0) begin
                wait(key_processed);
              end
              #1ps; // delay 1 ps to make sure did not sample right at negedge clk
              cfg.clk_rst_vif.wait_n_clks(1);
              hmac_rd_cnt++;
              `uvm_info(`gfn, $sformatf("increase rd cnt %0d", hmac_rd_cnt), UVM_HIGH)
              if (hmac_rd_cnt % HMAC_MSG_FIFO_DEPTH == 0) begin
                cfg.clk_rst_vif.wait_n_clks(HMAC_MSG_PROCESS_CYCLES);
              end
            end
            begin : reset_hmac_fifo_rd
              wait(cfg.under_reset);
            end
          join_any
          disable fork;
        end // end forever
      end
    join_none
  endtask

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacMsgFifoEmpty], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacDone], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacErr], 1'b0)
  endfunction

  // query the sha / hmac c model to get expected digest
  // update predicted digest to ral mirrored value
  virtual function void predict_digest(
    bit [7:0] msg_q[],
    bit       sha_en      = ral.cfg.sha_en.get_mirrored_value(),
    bit       hmac_en     = ral.cfg.hmac_en.get_mirrored_value(),
    bit [3:0] digest_size = ral.cfg.digest_size.get_mirrored_value(),
    bit [4:0] key_length  = ral.cfg.key_length.get_mirrored_value());
    exp_digest = '{default:0}; // clear previous expected digest

    `uvm_info(`gfn, $sformatf("Computing digest prediction"), UVM_LOW)

    // TODO: predict even if sha_en == 0?
    case ({hmac_en, sha_en})
      2'b11: begin
        if (digest_size == SHA2_256) begin
          if (key_length == Key_128) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:3], msg_q, exp_digest[0:7]);
          end else if (key_length == Key_256) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:7], msg_q, exp_digest[0:7]);
          end else if (key_length == Key_384) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:11], msg_q, exp_digest[0:7]);
          end else if (key_length == Key_512) begin
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:15], msg_q, exp_digest[0:7]);
          end else if (key_length == Key_1024) begin
            // model how the HW will limit key length to max of block size
            cryptoc_dpi_pkg::sv_dpi_get_hmac_sha256(key[0:15], msg_q, exp_digest[0:7]);
          end
        end else if (digest_size == SHA2_384) begin
          if (key_length == Key_128) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:3], msg_q, exp_digest[0:11]);
          if (key_length == Key_256) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:7], msg_q, exp_digest[0:11]);
          if (key_length == Key_384) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:11], msg_q, exp_digest[0:11]);
          if (key_length == Key_512) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:15], msg_q, exp_digest[0:11]);
          if (key_length == Key_1024) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha384(
                                                      key[0:31], msg_q, exp_digest[0:11]);
        end else if (digest_size == SHA2_512) begin
          if (key_length == Key_128) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:3], msg_q, exp_digest);
          if (key_length == Key_256) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:7], msg_q, exp_digest);
          if (key_length == Key_384) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:11], msg_q, exp_digest);
          if (key_length == Key_512) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:15], msg_q, exp_digest);
          if (key_length == Key_1024) cryptoc_dpi_pkg::sv_dpi_get_hmac_sha512(
                                                      key[0:31], msg_q, exp_digest);
        end
      `uvm_info(`gfn, $sformatf("HMAC of key=%p, msq_q=%p: %p", key, msg_q, exp_digest), UVM_LOW)
      end
      2'b01: begin
        if (digest_size == SHA2_256) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha256_digest(msg_q, exp_digest[0:7]);
        end else if (digest_size == SHA2_384) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha384_digest(msg_q, exp_digest[0:11]);
        end else if (digest_size == SHA2_512) begin
          cryptoc_dpi_pkg::sv_dpi_get_sha512_digest(msg_q, exp_digest);
        end
      `uvm_info(`gfn, $sformatf("SHA-2 digest of msq_q=%p: %p", msg_q, exp_digest), UVM_LOW)
      end
      default: begin
        // disgest is cleared if sha_en = 0
        exp_digest = '{default:0};
      end
    endcase
  endfunction

  virtual function void update_wr_msg_length(int size_bytes);
    uint64 size_bits = size_bytes * 8;
    void'(ral.msg_length_upper.predict(size_bits[TL_DW*2-1:TL_DW]));
    void'(ral.msg_length_lower.predict(size_bits[TL_DW-1:0]));
  endfunction

  virtual function void update_err_intr_code(err_code_e err_code_val);
    if (!ral.intr_state.hmac_err.get_mirrored_value()) begin
      void'(ral.intr_state.hmac_err.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));
      void'(ral.err_code.predict(.value(err_code_val), .kind(UVM_PREDICT_DIRECT)));
    end
  endfunction

  virtual function void check_idle_o(bit val);
    if (cfg.under_reset == 0) `DV_CHECK_EQ(cfg.hmac_vif.is_idle(), val)
  endfunction
endclass
