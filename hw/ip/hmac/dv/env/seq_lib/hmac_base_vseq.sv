// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_base_vseq extends cip_base_vseq #(.CFG_T               (hmac_env_cfg),
                                             .RAL_T               (hmac_reg_block),
                                             .COV_T               (hmac_env_cov),
                                             .VIRTUAL_SEQUENCER_T (hmac_virtual_sequencer));
  `uvm_object_utils(hmac_base_vseq)
  `uvm_object_new

  bit do_hmac_init     = 1'b1;
  bit do_back_pressure = 1'b0;
  bit do_burst_wr      = 1'b0;

  rand bit [TL_AW-1:0]    wr_addr;
  rand bit [TL_DBW-1:0]   wr_mask;
  rand bit                wr_config_during_hash;
  rand bit                wr_key_during_hash;
  rand bit                hmac_en;
  rand bit [3:0]          digest_size;
  rand bit [31:0]         key[NUM_KEYS];
  rand bit [5:0]          key_length;
  rand bit                endian_swap;
  rand bit                digest_swap;

  constraint wr_addr_c {
    wr_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]};
  }

  constraint wr_mask_c {
    $countones(wr_mask) dist {
      TL_DBW       :/ 1,
      [1:TL_DBW-1] :/ 1
    };
  }

constraint key_digest_c {
    $countones(key_length) == 1 dist {
      1 :/ 8,  // Key_128/Key_256/Key_384/Key_512/Key_1024/Key_None
      0 :/ 2   // Illegal -> should get casted to Key_None in HW
    };

    $countones(digest_size) == 1 dist {
      1 :/ 8,  // SHA2_256/SHA2_384/SHA2_512/SHA2_None
      0 :/ 2   // Illegal -> should get casted to SHA2_None in HW
    };
  }

  constraint wr_mask_contiguous_c {
    $countones(wr_mask ^ {wr_mask[TL_DBW-2:0], 1'b0}) <= 2; // mask must have contiguous ones
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if (do_hmac_init) hmac_init();
    `DV_CHECK_EQ(cfg.hmac_vif.is_idle(), 1'b1)
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.hash_process_triggered = 0;
  endtask

  virtual task hmac_init(bit sha_en             = 1'b1,
                         bit hmac_en            = 1'b1,
                         bit endian_swap        = 1'b1,
                         bit digest_swap        = 1'b1,
                         bit [3:0] digest_size  = 4'b0001, // SHA-256
                         bit [5:0] key_length   = 6'b00_0010, // 256-bit key
                         bit intr_fifo_empty_en = 1'b1,
                         bit intr_hmac_done_en  = 1'b1,
                         bit intr_hmac_err_en   = 1'b1);
    bit [TL_DW-1:0] interrupts;
    // enable sha, hmac data paths with digest size SHA-2 256
    // and 512-bit key and writing to msg_fifo
    ral.cfg.sha_en.set(sha_en);
    ral.cfg.hmac_en.set(hmac_en);
    ral.cfg.endian_swap.set(endian_swap);
    ral.cfg.digest_swap.set(digest_swap);
    ral.cfg.digest_size.set(digest_size);
    ral.cfg.key_length.set(key_length);
    csr_update(.csr(ral.cfg));

    // enable interrupts
    interrupts = (intr_hmac_err_en << HmacErr) | (intr_hmac_done_en << HmacDone) |
                 (intr_fifo_empty_en << HmacMsgFifoEmpty);
    cfg_interrupts(.interrupts(interrupts), .enable(1'b1));
  endtask

  virtual task write_discard_config_and_key(bit do_wr_config, bit do_wr_key);
    if (do_wr_config) write_discard_config();
    if (do_wr_key) begin
      write_discard_key();
      check_error_code(0);
    end
  endtask

  // keep all the config values, but enable sha_en
  virtual task sha_enable();
    ral.cfg.sha_en.set(1'b1);
    csr_update(.csr(ral.cfg));
  endtask

  // attempt to change config reg during msg write, design will ignore the change
  virtual task write_discard_config();
    bit [TL_DW-1:0] rand_config_value = $urandom();
    csr_wr(ral.cfg, rand_config_value);
  endtask

  virtual task write_discard_key();
    bit [TL_DW-1:0] rand_key_value = $urandom();
    int key_idx = $urandom_range(0, 31);
    csr_wr(ral.key[key_idx], rand_key_value);
  endtask

  // start hash computations
  virtual task trigger_hash();
    csr_wr(.ptr(ral.cmd), .value(1'b1 << HashStart));
    // If SHA is not enabled, check that an error is signaled.
    if (!ral.cfg.sha_en.get_mirrored_value()) check_error_code();
    `uvm_info(`gfn, "triggering hash to start", UVM_LOW)
  endtask

  // continue hash computations
  virtual task trigger_hash_continue();
    csr_wr(.ptr(ral.cmd), .value(1'b1 << HashContinue));
    // If SHA is not enabled, check that an error is signaled.
    if (!ral.cfg.sha_en.get_mirrored_value()) check_error_code();
  endtask

  // stop hash computations
  virtual task trigger_hash_stop();
    csr_wr(.ptr(ral.cmd), .value(1'b1 << HashStop));
  endtask

  // trigger calculation of digest at the end of a message
  virtual task trigger_process();
    // read digest size and key length and update their mirrored values
    csr_wr(.ptr(ral.cmd), .value(1'b1 << HashProcess));
    cfg.hash_process_triggered = 1;
  endtask

  virtual task trigger_hash_when_active();
    `uvm_info(`gfn, "triggering hash when active", UVM_LOW)
    repeat ($urandom_range(1, 10)) trigger_hash();
    check_error_code(0);
  endtask

  // read digest value
  virtual task rd_digest();
    bit [TL_DW-1:0] digest[16];
    csr_rd_digest(digest);
    // Clear the wipe_secret flag because the exp digest val in scb will be updated.
    clear_wipe_secret();
  endtask : rd_digest

  virtual function clear_wipe_secret();
    `uvm_info(`gfn, "wiping secret untriggered", UVM_LOW)
    cfg.wipe_secret_triggered = 0;
  endfunction : clear_wipe_secret

  // read digest value and output read value
  virtual task csr_rd_digest(output bit [TL_DW-1:0] digest[16]);
    foreach (digest[i]) begin
      csr_rd(.ptr(ral.digest[i]), .value(digest[i]));
      `uvm_info(`gfn, $sformatf("digest[%0d]=32'h%08x", i, digest[i]), UVM_MEDIUM)
    end
  endtask

  // write digest value
  virtual task csr_wr_digest(bit [TL_DW-1:0] digest[16]);
    foreach (digest[i]) csr_wr(.ptr(ral.digest[i]), .value(digest[i]));
  endtask

  // read digest size and update mirrored value
  virtual task csr_rd_digest_size(output bit [3:0] read_digest_size);
    csr_rd(.ptr(ral.cfg.digest_size), .value(read_digest_size));
    `uvm_info(`gfn, $sformatf("reading digest size: %04b", read_digest_size), UVM_MEDIUM)
  endtask

  // read key length and update mirrored value
  virtual task csr_rd_key_length(output bit [5:0] read_key_length);
    csr_rd(.ptr(ral.cfg.key_length), .value(read_key_length));
    `uvm_info(`gfn, $sformatf("reading key length: %06b", read_key_length), UVM_MEDIUM)
  endtask

  // write 1024-bit hashed key
  //
  // can safely assume that the input array will always have 32 elements
  // key_length determines how much of the key array is relevant for the HMAC operation
  virtual task wr_key(bit [TL_DW-1:0] key[]);
    foreach (key[i]) begin
      ral.key[i].set(key[i]);
      csr_update(.csr(ral.key[i]));
      `uvm_info(`gfn, $sformatf("key[%0d] = 0x%0h", i, key[i]), UVM_HIGH)
    end
  endtask

  virtual task wipe_secrets();
    bit [TL_DW-1:0] secret_val;
    `DV_CHECK_STD_RANDOMIZE_FATAL(secret_val)
    csr_wr(.ptr(ral.wipe_secret), .value(secret_val));
    cfg.wipe_secret_triggered = 1;
    `uvm_info(`gfn, $sformatf("wipe secret triggered"), UVM_LOW)
  endtask

  // write msg to DUT, read status FIFO FULL and check intr FIFO FULL
  virtual task wr_msg(bit [7:0] msg[], bit non_blocking = $urandom_range(0, 1));
    int bits_written = 0;
    bit [7:0] msg_q[$] = msg;
    // randomly pick the size of bytes to write
    // unless msg size is smaller than randomized size
    while (msg_q.size() > 0) begin
      bit [7:0] word_unpack[4];
      bit [TL_DW-1:0] word;
      `DV_CHECK_FATAL(randomize(wr_addr, wr_mask) with {$countones(wr_mask) <= msg_q.size();})
      foreach (wr_mask[i]) begin
        // wr_mask is a packed array, word_unpacked is unpack, has different index
        if (wr_mask[i]) word_unpack[3 - i] = msg_q.pop_front();
        else word_unpack[3 - i] = $urandom();
      end
      word = {>>byte{word_unpack}};
      `uvm_info(`gfn, $sformatf("wr_addr = %0h, wr_mask = %0h, words = 0x%0h",
                                wr_addr, wr_mask, word), UVM_LOW)
      tl_access(.addr(cfg.ral.get_addr_from_offset(wr_addr)),
                .write(1'b1), .data(word), .mask(wr_mask), .blocking(non_blocking));
      bits_written += $countones(wr_mask) * 8;

      `uvm_info(`gfn, $sformatf("bits written: %0d", bits_written), UVM_HIGH)

      if (bits_written % 512 == 0 && msg_q.size() > 0 &&
          cfg.save_and_restore_pct > $urandom_range(0, 99)) begin
        // Multiple of block size reached; this is an opportunity to save the digest by reading it
        // from SW, then disable SHA, reload the digest, and continue message processing.
        // TODO: When adding SHA-384/512, the `512` (i.e., the block size) above must be dynamically
        // changed between 512 (for SHA-256) and 1024 (for SHA-384/512).
        bit [TL_DW-1:0] digest[16];
        bit [2*TL_DW-1:0] msg_length;
        `uvm_info(`gfn, $sformatf("Saving and restoring context"), UVM_LOW)
        // Ensure all messages have been written to FIFO (in case the `tl_access`es above were
        // non-blocking).
        csr_utils_pkg::wait_no_outstanding_access();
        // Stop hash operations.
        trigger_hash_stop();
        // Wait for hash to be done so the digest is updated.
        csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
        // Clear the interrupt.
        csr_wr(.ptr(ral.intr_state.hmac_done), .value(1'b1));
        // Read the digest to save it.
        csr_rd_digest(digest);
        // Read message length.
        csr_rd_msg_length(msg_length);
        // Disable SHA so we can write digest and message length.
        csr_wr(.ptr(ral.cfg.sha_en), .value(1'b0));
        // Clearing the message length is not strictly necessary but currently done to ensure the
        // previous value does not persist.
        csr_wr_msg_length('0); //
        // Reload the digest by writing it back.
        csr_wr_digest(digest);
        // Reload the message length by writing it back.
        csr_wr_msg_length(msg_length);
        // Re-enable SHA and continue hashing.
        csr_wr(.ptr(ral.cfg.sha_en), .value(1'b1));
        trigger_hash_continue();
      end

      if (ral.cfg.sha_en.get_mirrored_value()) begin
        if (!do_back_pressure) begin
          if ($urandom_range(0, 1)) read_status_intr_clr();
        end
        // randomly change key, config regs during msg wr, should trigger error or be discarded
        write_discard_config_and_key(wr_config_during_hash, wr_key_during_hash);
      end else begin
        check_error_code();
      end
    end
    // ensure all msg fifo are written before trigger hmac_process
    csr_utils_pkg::wait_no_outstanding_access();
    if ($urandom_range(0, 1)) rd_msg_length();
    read_status_intr_clr();
  endtask

  // read fifo_depth reg and burst write a chunk of words
  virtual task burst_wr_msg(bit [7:0] msg[], int burst_wr_length);
    bit [7:0]       msg_q[$] = msg;
    bit [7:0]       word_unpack[4];
    bit [TL_DW-1:0] word;
    while (msg_q.size() > 0) begin
      // wait until HMAC has enough space to burst write
      csr_spinwait(.ptr(ral.status.fifo_depth),
                   .exp_data(HMAC_MSG_FIFO_DEPTH - burst_wr_length),
                   .compare_op(CompareOpLe));
      if (msg_q.size() >= burst_wr_length * 4) begin
        repeat (burst_wr_length) begin
          for (int i = 0; i < 4; i++) word_unpack[i] = msg_q.pop_front();
          word = {>>byte{word_unpack}};
          `uvm_info(`gfn, $sformatf("wr_addr = %0h, wr_mask = %0h, words = 0x%0h",
                                    wr_addr, wr_mask, word), UVM_HIGH)
          `DV_CHECK_FATAL(randomize(wr_addr, wr_mask) with {wr_mask == '1;})
          tl_access(.addr(cfg.ral.get_addr_from_offset(wr_addr)),
                    .write(1'b1), .data(word), .mask(wr_mask), .blocking($urandom_range(0, 1)));
        end
        // Expected error as we may not push message into the FIFO while SHA is disabled
        if (!ral.cfg.sha_en.get_mirrored_value()) begin
          check_error_code();
        end
      end else begin // remaining msg is smaller than the burst_wr_length
        wr_msg(msg_q);
        break;
      end
      csr_utils_pkg::wait_no_outstanding_access();
      if ($urandom_range(0, 1)) rd_msg_length();
      read_status_intr_clr();
    end
  endtask

  // read the message length from the DUT reg (but discard it)
  virtual task rd_msg_length();
    bit [2*TL_DW-1:0] unused;
    csr_rd_msg_length(unused);
  endtask

  // read the message length from the DUT reg
  virtual task csr_rd_msg_length(output bit [2*TL_DW-1:0] msg_length);
    csr_rd(ral.msg_length_upper, msg_length[2*TL_DW-1:TL_DW]);
    csr_rd(ral.msg_length_lower, msg_length[TL_DW-1:0]);
  endtask

  // write message length to the DUT reg
  virtual task csr_wr_msg_length(bit [2*TL_DW-1:0] msg_length);
    csr_wr(.ptr(ral.msg_length_upper), .value(msg_length[2*TL_DW-1:TL_DW]));
    csr_wr(.ptr(ral.msg_length_lower), .value(msg_length[TL_DW-1:0]));
  endtask

  // read status and interrupt state and clear the interrupt state
  virtual task read_status_intr_clr();
    bit [TL_DW-1:0] rdata;
    csr_utils_pkg::wait_no_outstanding_access();
    csr_rd(ral.status, rdata);
    csr_rd(ral.intr_state, rdata);
    csr_wr(.ptr(ral.intr_state), .value(rdata));
  endtask

  // this task is called when sha_en=0 and sequence set hash_start, or streamed in msg
  // it will check intr_pin, intr_state, and error_code register
  // default check_err is 1, if set to 0, means user is not sure if it is error case or not,
  // will leave the checking to scoreboard
  virtual task check_error_code(bit check_err = 1);
    bit [TL_DW-1:0] error_code;
    csr_utils_pkg::wait_no_outstanding_access();
    if (check_err) begin
      if (ral.intr_enable.hmac_err.get_mirrored_value()) begin
        check_interrupts(.interrupts((1 << HmacErr)), .check_set(1'b1));
      end else begin
        csr_rd_check(.ptr(ral.intr_state), .compare_value(1 << HmacErr));
        csr_wr(.ptr(ral.intr_state), .value(1 << HmacErr));
      end
    end else begin
      csr_rd(.ptr(ral.intr_state), .value(error_code));
      csr_wr(.ptr(ral.intr_state), .value(error_code));
    end
    csr_rd(ral.err_code, error_code);
  endtask

  virtual task compare_digest(bit [7:0] exp_digest[]);
    bit [TL_DW-1:0] act_digest[16];
    bit [TL_DW-1:0] packed_exp_digest[8];
    csr_rd_digest(act_digest);
    // `exp_digest` is guaranteed to always contain 16 words (64 bytes) of data
    // since HMAC digest size is max 512 bits.
    packed_exp_digest = {>>byte{exp_digest}};
    if (cfg.clk_rst_vif.rst_n) begin
      // can safely assume that `exp_digest` always has 16 elements
      // since HMAC output digest size is 512 bits.
      foreach (act_digest[i]) begin
        `uvm_info(`gfn, $sformatf("Actual digest[%0d]: 0x%0h", i, act_digest[i]), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("Expected digest[%0d]: 0x%0h", i, packed_exp_digest[i]), UVM_HIGH)
      end

      // comparing for SHA-2 256
      foreach (act_digest[i]) begin
        if (i < 8) begin
          `DV_CHECK_EQ(act_digest[i], packed_exp_digest[i], $sformatf("for index %0d", i))
        end else begin
          `DV_CHECK_EQ(act_digest[i], '0);
        end
      end
    end else begin
      `uvm_info(`gfn, "skipped comparison due to reset", UVM_LOW)
    end
  endtask

endclass : hmac_base_vseq
