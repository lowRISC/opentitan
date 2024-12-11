// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_base_vseq extends cip_base_vseq #(.CFG_T               (hmac_env_cfg),
                                             .RAL_T               (hmac_reg_block),
                                             .COV_T               (hmac_env_cov),
                                             .VIRTUAL_SEQUENCER_T (hmac_virtual_sequencer));
  `uvm_object_utils(hmac_base_vseq)

  // Control knobs
  bit do_hmac_init      = 1'b1;
  bit do_back_pressure  = 1'b0;
  bit do_burst_wr       = 1'b0;

  bit       invalid_cfg;
  bit [5:0] cast_key_length;
  bit [3:0] cast_digest_size;

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
  rand bit                key_swap;

  // Local variables
  // Keep context configuration while testing Save and Restore feature
  local bit               endian_swap_bak;
  local bit               digest_swap_bak;
  local bit               key_swap_bak;
  local bit [3:0]         digest_size_bak;
  local bit [5:0]         key_length_bak;
  local bit [TL_DW-1:0]   key_bak[];
  local uvm_event         sar_window    = new();
  local uvm_event         hash_continue = new();
  local bit               save_ctx_ongoing;
  local bit               sar_ongoing;

  // Constraints
  extern constraint wr_addr_c;
  extern constraint wr_mask_c;
  extern constraint key_length_c;
  extern constraint digest_size_c;
  extern constraint wr_mask_contiguous_c;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern task dut_init(string reset_kind = "HARD");
  extern task apply_reset(string kind = "HARD");
  extern task hmac_init(bit sha_en = 1'b1, bit hmac_en = 1'b1, bit endian_swap = 1'b1,
    bit digest_swap = 1'b1, bit key_swap  = 1'b0, bit [3:0] digest_size = 4'b0001,
    bit [5:0] key_length = 6'b00_0010, bit intr_fifo_empty_en = 1'b1, bit intr_hmac_done_en = 1'b1,
    bit intr_hmac_err_en = 1'b1);
  extern task write_discard_config_and_key(bit do_wr_config, bit do_wr_key);
  extern task sha_enable();
  extern task write_discard_config();
  extern task write_discard_key();
  extern task trigger_hash();
  extern task trigger_hash_continue();
  extern task trigger_hash_stop();
  extern task trigger_process();
  extern task trigger_hash_when_active();
  extern task rd_digest();
  extern function void clear_wipe_secret();
  extern task csr_rd_digest(output bit [TL_DW-1:0] digest[16]);
  extern task csr_wr_digest(bit [TL_DW-1:0] digest[16]);
  extern task csr_rd_digest_size(output bit [3:0] read_digest_size);
  extern task csr_rd_key_length(output bit [5:0] read_key_length);
  // Write 1024-bit hashed key
  extern task wr_key(bit [TL_DW-1:0] key[]);
  extern task wipe_secrets();
  // Write into DUT's message FIFO
  extern task wr_msg(bit [7:0] msg[], bit no_sar=0);
  // Burst write a chunk of words into DUT's message FIFO
  extern task burst_wr_msg(bit [7:0] msg[], int burst_wr_length);
  // Read the message length from the DUT reg (but discard it)
  extern task rd_msg_length();
  // Read the message length from the DUT reg
  extern task csr_rd_msg_length(output bit [2*TL_DW-1:0] msg_length);
  // Write message length to the DUT reg
  extern task csr_wr_msg_length(bit [2*TL_DW-1:0] msg_length);
  // Read status and interrupt state and clear the interrupt state
  extern task read_status_intr_clr();
  // Check intr_pin, intr_state, and error_code registers
  extern task check_error_code(bit check_err = 1);
  extern task compare_digest(bit [7:0] exp_digest[], int tag_len_byte, bit [3:0] digest_size_i);
  extern task save_and_restore();
  extern task sar_stop_and_continue();
  extern task sar_same_context();
  extern task sar_different_context();
  extern task save_and_restore_cfg(bit save_current_cfg, bit restore_previous_cfg);
  extern function int wait_cycles_with_no_outstanding_accesses();
endclass : hmac_base_vseq


constraint hmac_base_vseq::wr_addr_c {
  wr_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]};
}

constraint hmac_base_vseq::wr_mask_c {
  $countones(wr_mask) dist {
    TL_DBW       :/ 1,
    [1:TL_DBW-1] :/ 1
  };
}

constraint hmac_base_vseq::key_length_c {
  $countones(key_length) == 1 dist {
    1 :/ 4,  // Key_128/Key_256/Key_384/Key_512/Key_1024/Key_None
    0 :/ 1   // Illegal -> should get casted to Key_None in HW
  };
}

constraint hmac_base_vseq::digest_size_c {
  $countones(digest_size) == 1 dist {
    1 :/ 4,  // SHA2_256/SHA2_384/SHA2_512/SHA2_None
    0 :/ 1   // Illegal -> should get casted to SHA2_None in HW
  };
}

constraint hmac_base_vseq::wr_mask_contiguous_c {
  $countones(wr_mask ^ {wr_mask[TL_DBW-2:0], 1'b0}) <= 2; // mask must have contiguous ones
}

function hmac_base_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init(reset_kind);
  if (do_hmac_init) begin
    hmac_init();
  end
  `DV_CHECK_EQ(cfg.hmac_vif.is_idle(), 1'b1)
endtask : dut_init

task hmac_base_vseq::apply_reset(string kind = "HARD");
  super.apply_reset(kind);
  cfg.hash_process_triggered = 0;
endtask : apply_reset

task hmac_base_vseq::hmac_init( bit sha_en             = 1'b1,
                                bit hmac_en            = 1'b1,
                                bit endian_swap        = 1'b1,
                                bit digest_swap        = 1'b1,
                                bit key_swap           = 1'b0,
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
  ral.cfg.key_swap.set(key_swap);
  ral.cfg.digest_size.set(digest_size);
  ral.cfg.key_length.set(key_length);
  csr_update(.csr(ral.cfg));

  // read digest size and key length after casting from CSRs and update mirrored values
  csr_rd_digest_size(cast_digest_size);
  csr_rd_key_length(cast_key_length);

  // indicate if config is invalid and would block triggering the hash to start
  if ((cast_digest_size == SHA2_None) ||
      ((cast_key_length == Key_None) && hmac_en) ||
      ((cast_digest_size == SHA2_256) && (cast_key_length == Key_1024) && hmac_en)) begin
    invalid_cfg = 1;
  end else begin
    invalid_cfg = 0;
  end

  `uvm_info(`gfn, $sformatf("invalid config: %1b", invalid_cfg), UVM_LOW)

  // enable interrupts
  interrupts = (intr_hmac_err_en << HmacErr) | (intr_hmac_done_en << HmacDone) |
               (intr_fifo_empty_en << HmacMsgFifoEmpty);
  cfg_interrupts(.interrupts(interrupts), .enable(1'b1));
endtask : hmac_init

task hmac_base_vseq::write_discard_config_and_key(bit do_wr_config, bit do_wr_key);
  if (do_wr_config) begin
    write_discard_config();
  end
  if (do_wr_key) begin
    write_discard_key();
    check_error_code(0);
  end
endtask : write_discard_config_and_key

// Keep all the config values, but enable sha_en
task hmac_base_vseq::sha_enable();
  ral.cfg.sha_en.set(1'b1);
  csr_update(.csr(ral.cfg));
endtask : sha_enable

// Attempt to change config reg during msg write, design will ignore the change
task hmac_base_vseq::write_discard_config();
  bit [TL_DW-1:0] rand_config_value = $urandom();
  csr_wr(ral.cfg, rand_config_value);
endtask : write_discard_config

task hmac_base_vseq::write_discard_key();
  bit [TL_DW-1:0] rand_key_value = $urandom();
  int key_idx = $urandom_range(0, 31);
  csr_wr(ral.key[key_idx], rand_key_value);
endtask : write_discard_key

// Start hash computations
task hmac_base_vseq::trigger_hash();
  `uvm_info(`gfn, "triggering hash to start", UVM_LOW)
  csr_wr(.ptr(ral.cmd), .value(1'b1 << HashStart));
  // If incorrectly configured or SHA is not enabled, check that an error is signaled.
  if (invalid_cfg || !`gmv(ral.cfg.sha_en)) begin
    check_error_code();
  end
endtask : trigger_hash

// Continue hash computations
task hmac_base_vseq::trigger_hash_continue();
  `uvm_info(`gfn, "triggering hash to continue", UVM_LOW)
  csr_wr(.ptr(ral.cmd), .value(1'b1 << HashContinue));
  // If SHA is not enabled, check that an error is signaled.
  if (!`gmv(ral.cfg.sha_en)) begin
    check_error_code();
  end
  // Should be triggered while B context to freeze wr_msg/burst_wr_msg as continue will
  // be triggered to check a fictive B context with a large msg_length
  if (!cfg.sar_skip_ctxt) begin
    hash_continue.trigger();
  end
endtask : trigger_hash_continue

// Stop hash computations
task hmac_base_vseq::trigger_hash_stop();
  `uvm_info(`gfn, "triggering hash to stop", UVM_LOW)
  csr_wr(.ptr(ral.cmd), .value(1'b1 << HashStop));
endtask : trigger_hash_stop

// Trigger calculation of digest at the end of a message only when Save and Restore hasn't been
// triggered before
task hmac_base_vseq::trigger_process();
  if (!save_ctx_ongoing) begin
    `uvm_info(`gfn, "triggering hash to process", UVM_LOW)
    csr_wr(.ptr(ral.cmd), .value(1'b1 << HashProcess));
    cfg.hash_process_triggered = 1;
  end
endtask : trigger_process

task hmac_base_vseq::trigger_hash_when_active();
  `uvm_info(`gfn, "triggering hash when active", UVM_LOW)
  repeat ($urandom_range(1, 10)) trigger_hash();
  check_error_code(0);
endtask : trigger_hash_when_active

// Read digest value
task hmac_base_vseq::rd_digest();
  bit [TL_DW-1:0] digest[16];
  csr_rd_digest(digest);
endtask : rd_digest

function void hmac_base_vseq::clear_wipe_secret();
  `uvm_info(`gfn, "wiping secret untriggered", UVM_LOW)
  cfg.wipe_secret_triggered = 0;
endfunction : clear_wipe_secret

// Read digest value and output read value
task hmac_base_vseq::csr_rd_digest(output bit [TL_DW-1:0] digest[16]);
  foreach (digest[i]) begin
    csr_rd(.ptr(ral.digest[i]), .value(digest[i]));
    `uvm_info(`gfn, $sformatf("digest[%0d]=32'h%08x", i, digest[i]), UVM_MEDIUM)
  end
endtask : csr_rd_digest

// Write digest value
task hmac_base_vseq::csr_wr_digest(bit [TL_DW-1:0] digest[16]);
  foreach (digest[i]) csr_wr(.ptr(ral.digest[i]), .value(digest[i]));
endtask : csr_wr_digest

// Read digest size and update mirrored value
task hmac_base_vseq::csr_rd_digest_size(output bit [3:0] read_digest_size);
  csr_rd(.ptr(ral.cfg.digest_size), .value(read_digest_size));
  `uvm_info(`gfn, $sformatf("reading digest size: %04b", read_digest_size), UVM_MEDIUM)
endtask : csr_rd_digest_size

// Read key length and update mirrored value
task hmac_base_vseq::csr_rd_key_length(output bit [5:0] read_key_length);
  csr_rd(.ptr(ral.cfg.key_length), .value(read_key_length));
  `uvm_info(`gfn, $sformatf("reading key length: %06b", read_key_length), UVM_MEDIUM)
endtask : csr_rd_key_length

// Can safely assume that the input array will always have 32 elements
// key_length determines how much of the key array is relevant for the HMAC operation
task hmac_base_vseq::wr_key(bit [TL_DW-1:0] key[]);
  foreach (key[i]) begin
    ral.key[i].set(key[i]);
    csr_update(.csr(ral.key[i]));
    `uvm_info(`gfn, $sformatf("key[%0d] = 0x%0h", i, key[i]), UVM_HIGH)
  end
endtask : wr_key

task hmac_base_vseq::wipe_secrets();
  bit [TL_DW-1:0] secret_val;
  `DV_CHECK_STD_RANDOMIZE_FATAL(secret_val)
  csr_wr(.ptr(ral.wipe_secret), .value(secret_val));
  cfg.wipe_secret_triggered = 1;
  `uvm_info(`gfn, $sformatf("wiping secret triggered"), UVM_LOW)
endtask : wipe_secrets

// Write msg to DUT, read status FIFO FULL and check intr FIFO FULL
// Spawn a Save and Restore thread only when needed (as burst_wr_msg might call this task also
// while the sar_thread is already ongoing)
task hmac_base_vseq::wr_msg(bit [7:0] msg[], bit no_sar=0);
  int bits_written = 0;
  bit [7:0] msg_q[$] = msg;

  // Spawn save and restore task only on some occasions
  fork : sar_simple_thread
    begin
      if (!invalid_cfg && !no_sar && !sar_ongoing && (sar_window.get_num_waiters() == 0) &&
          (cfg.save_and_restore_pct > $urandom_range(0, 99)) && (msg_q.size() > 0)) begin
        save_and_restore();
      end
    end
    begin
      // randomly pick the size of bytes to write
      // unless msg size is smaller than randomized size
      while (msg_q.size() > 0) begin
        bit [7:0] word_unpack[4];
        bit [TL_DW-1:0] word;
        `DV_CHECK_FATAL(randomize(wr_addr, wr_mask) with {$countones(wr_mask) <= msg_q.size();})

        foreach (wr_mask[i]) begin
          // wr_mask is a packed array, word_unpacked is unpack, has different index
          if (wr_mask[i]) begin
            word_unpack[3 - i] = msg_q.pop_front();
          end else begin
            word_unpack[3 - i] = $urandom();
          end
        end
        word = {>>byte{word_unpack}};
        `uvm_info(`gfn, $sformatf("wr_addr = %0h, wr_mask = %04b, words = 0x%0h",
                                  wr_addr, wr_mask, word), UVM_LOW)
        tl_access(.addr(cfg.ral.get_addr_from_offset(wr_addr)),
                  .write(1'b1), .data(word), .mask(wr_mask), .blocking(1));
        bits_written += $countones(wr_mask) * 8;

        `uvm_info(`gfn, $sformatf("bits written: %0d", bits_written), UVM_HIGH)

        // Block size has to be not zero to avoid to divide by zero
        if (get_block_size(digest_size) != 0) begin
          // Multiple of block size reached => opportunity to trigger a save and restore sequence
          // Only when message is not completely yet transmitted, as it doesn't make sense
          if ((bits_written % get_block_size(digest_size) == 0) && (msg_q.size() > 0)) begin
            // Trigger the event only if someone is waiting for it, this is to prevent infinite
            // wait in case of a S&R is triggered 2 times for a same message
            if (sar_window.get_num_waiters() > 0) begin
              sar_window.trigger();
              hash_continue.wait_trigger();
            end
          end
        end

        if (`gmv(ral.cfg.sha_en)) begin
          if (!do_back_pressure) begin
            if ($urandom_range(0, 1)) begin
              read_status_intr_clr();
            end
          end
          // randomly change key, config regs during msg wr, should trigger error or be discarded
          write_discard_config_and_key(wr_config_during_hash, wr_key_during_hash);
          // Randomly trigger error code read also when no error is supposed to happen
          if ($urandom_range(0, 1)) begin
            check_error_code(0);
          end
        end else begin
          check_error_code(1);
        end
      end
      // Keep it alive only if needed
      if (!sar_ongoing) begin
        disable sar_simple_thread;
        sar_window.reset();
      end
    end
  join
  sar_window.reset();
  // ensure all msg fifo are written before trigger hmac_process
  if ($urandom_range(0, 1)) begin
    rd_msg_length();
  end
  read_status_intr_clr();
endtask : wr_msg

// Read fifo_depth reg and burst write a chunk of words
task hmac_base_vseq::burst_wr_msg(bit [7:0] msg[], int burst_wr_length);
  bit [7:0]       msg_q[$] = msg;
  bit [7:0]       word_unpack[4];
  bit [TL_DW-1:0] word;
  int             bits_written = 0;

  // Spawn save and restore task only on some occasions
  fork : sar_burst_thread
    begin
      if (!invalid_cfg && !sar_ongoing && (sar_window.get_num_waiters() == 0) &&
          (cfg.save_and_restore_pct > $urandom_range(0, 99)) && (msg_q.size() > 0)) begin
        save_and_restore();
      end
    end
    begin
      while (msg_q.size() > 0) begin
        // wait until HMAC has enough space to burst write
        csr_spinwait(.ptr(ral.status.fifo_depth),
                    .exp_data(HMAC_MSG_FIFO_DEPTH_WR - burst_wr_length),
                    .compare_op(CompareOpLe));
        if (msg_q.size() >= burst_wr_length * 4) begin
          repeat (burst_wr_length) begin
            for (int i = 0; i < 4; i++) word_unpack[i] = msg_q.pop_front();
            word = {>>byte{word_unpack}};
            `uvm_info(`gfn, $sformatf("wr_addr = %0h, wr_mask = %0h, words = 0x%0h",
                                      wr_addr, wr_mask, word), UVM_HIGH)
            `DV_CHECK_FATAL(randomize(wr_addr, wr_mask) with {wr_mask == '1;})
            tl_access(.addr(cfg.ral.get_addr_from_offset(wr_addr)),
                      .write(1'b1), .data(word), .mask(wr_mask), .blocking(1));
            bits_written += $countones(wr_mask) * 8;

            `uvm_info(`gfn, $sformatf("bits written: %0d", bits_written), UVM_HIGH)

            // Block size has to be not zero to avoid to divide by zero
            if (get_block_size(digest_size) != 0) begin
              // Multiple of block size reached => opportunity to trigger a S&R sequence
              // Only when message is not completely yet transmitted, as it doesn't make sense
              if ((bits_written % get_block_size(digest_size) == 0) && (msg_q.size() > 0)) begin
                // Trigger the event only if someone is waiting for it, this is to prevent
                // infinite wait in case of a S&R is triggered 2 times for a same message
                if (sar_window.get_num_waiters() > 0) begin
                  sar_window.trigger();
                  hash_continue.wait_trigger();
                end
              end
            end
          end
          // Expected error as we may not push message into the FIFO while SHA is disabled
          if (!`gmv(ral.cfg.sha_en)) begin
            check_error_code();
          end
        // remaining msg is smaller than the burst_wr_length
        end else begin
          wr_msg(msg_q, 1); // Do not S&R on the last piece as message boundary could be wrong
          msg_q.delete();   // Flush the queue to avoid infinite loop
        end
        if ($urandom_range(0, 1)) begin
          rd_msg_length();
        end
        read_status_intr_clr();
      end
      // Keep it alive only if needed
      if (!sar_ongoing) begin
        disable sar_burst_thread;
        sar_window.reset();
      end
    end
  join
  sar_window.reset();
endtask : burst_wr_msg

task hmac_base_vseq::rd_msg_length();
  bit [2*TL_DW-1:0] unused;
  csr_rd_msg_length(unused);
endtask : rd_msg_length

task hmac_base_vseq::csr_rd_msg_length(output bit [2*TL_DW-1:0] msg_length);
  csr_rd(ral.msg_length_upper, msg_length[2*TL_DW-1:TL_DW]);
  csr_rd(ral.msg_length_lower, msg_length[TL_DW-1:0]);
endtask : csr_rd_msg_length

task hmac_base_vseq::csr_wr_msg_length(bit [2*TL_DW-1:0] msg_length);
  csr_wr(.ptr(ral.msg_length_upper), .value(msg_length[2*TL_DW-1:TL_DW]));
  csr_wr(.ptr(ral.msg_length_lower), .value(msg_length[TL_DW-1:0]));
endtask : csr_wr_msg_length

task hmac_base_vseq::read_status_intr_clr();
  bit [TL_DW-1:0] rdata;
  csr_rd(ral.status, rdata);
  csr_rd(ral.intr_state, rdata);
  csr_wr(.ptr(ral.intr_state), .value(rdata));
endtask : read_status_intr_clr
// This task is called when sha_en=0 and sequence set hash_start, or streamed in msg.
// It will check intr_pin, intr_state, and error_code registers.
// Default check_err is 1, if set to 0, means user is not sure if it is error case or not,
// will leave the checking to scoreboard
task hmac_base_vseq::check_error_code(bit check_err = 1);
  bit [TL_DW-1:0] error_code;
  if (check_err) begin
    if (`gmv(ral.intr_enable.hmac_err)) begin
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
  `uvm_info(`gfn, $sformatf("Error code: 0x%0h", error_code), UVM_HIGH)
endtask : check_error_code

// TODO (#23288): remove this check from the seq
task hmac_base_vseq::compare_digest(bit [7:0] exp_digest[], int tag_len_byte, bit [3:0] digest_size_i);
  bit [TL_DW-1:0] act_digest[16];
  bit [TL_DW-1:0] packed_exp_digest[16];
  csr_rd_digest(act_digest);
  // `exp_digest` is guaranteed to always contain 16 words (64 bytes) of data
  // since HMAC digest size is max 512 bits.
  packed_exp_digest = {>>byte{exp_digest}};
  if (cfg.clk_rst_vif.rst_n) begin
    foreach (act_digest[i]) begin
        // for HMAC test vectors:
        //  -only compare up to expected tag length (parsed in for each test vector)
        //  -which is always divisble by 4 (word-aligned) --> (tag_len_byte/4)
        // for SHA-2 (!hmac_en) test vectors:
        //  -compare up to the correct digest index depending on the digest size
      if ((hmac_en  && (i < (tag_len_byte/4))) ||
          (!hmac_en &&
            ((i  < 8) ||
            ((i >= 8 && i < 12) && (digest_size_i == SHA2_384 || digest_size_i == SHA2_512)) ||
            ((i >= 12)          && (digest_size_i == SHA2_512))))) begin

          `uvm_info(`gfn, $sformatf("Actual digest[%0d]: 0x%0h", i, act_digest[i]), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("Expected digest[%0d]: 0x%0h", i,
                    packed_exp_digest[i]), UVM_HIGH)
          `DV_CHECK_EQ(act_digest[i], packed_exp_digest[i], $sformatf("for index %0d", i))
      end
    end
  end else begin
    `uvm_info(`gfn, "skipped comparison due to reset", UVM_LOW)
  end
endtask : compare_digest

// Stop hash, save current context, do something/nothing and restore context
//    - Test with context A saved and restored
//    - Test with context A and B, alternatively saved and restored. Ensure to randomize again:
//      key length, digest size, digest swap, endian swap and secret key
task hmac_base_vseq::save_and_restore();
  // Wait until message transmission is on a block boundary (multiple of 512 bits in SHA-2 256
  // or 1024 bits SHA-2 384/512)
  sar_window.wait_trigger();

  // Insert random delay to mimic the SW accesses which can take some time because of potential
  // incoming interrupts. To cover the particular case where the stop command is issued while the
  // hash has already been processed, this delay should exceed the number clock cycles required
  // for this operation, which is 64 for SHA2-256 and 80 for SHA2-384/512 with the current RTL.
  cfg.clk_rst_vif.wait_clks($urandom_range(HMAC_MSG_PROCESS_CYCLES_256-10,
                                           HMAC_MSG_PROCESS_CYCLES_512+10));

  randcase
    1:  sar_stop_and_continue();
    1:  sar_same_context();
    1:  sar_different_context();
  endcase
endtask : save_and_restore

task hmac_base_vseq::sar_stop_and_continue();
  uvm_event sar_stop_continue_ev;

  sar_stop_continue_ev = uvm_event_sar_pool::get_global("sar_stop_and_continue_event");
  `uvm_info(`gfn, $sformatf("Stop and trigger continue only"), UVM_LOW)
  sar_ongoing = 1;
  // Stop hash operations.
  trigger_hash_stop();
  // Expose ongoing Save and Restore triggered to avoid to request a new hash process
  save_ctx_ongoing = 1;
  // Wait for hash to be done so the digest is updated.
  csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
  // Clear the interrupt.
  csr_wr(.ptr(ral.intr_state.hmac_done), .value(1'b1));
  save_ctx_ongoing = 0;
  trigger_hash_continue();
  sar_stop_continue_ev.trigger();
  sar_ongoing = 0;
endtask : sar_stop_and_continue;

task hmac_base_vseq::sar_same_context();
  bit [TL_DW-1:0]     digest_a[16];
  bit [2*TL_DW-1:0]   msg_length_a;
  uvm_event           sar_same_ctxt_ev;

  sar_same_ctxt_ev = uvm_event_sar_pool::get_global("sar_same_context_event");
  `uvm_info(`gfn, $sformatf("Saving and restoring with the same context"), UVM_LOW)
  sar_ongoing = 1;
  // Stop hash operations.
  trigger_hash_stop();
  // Expose ongoing Save and Restore triggered to avoid to request a new hash process
  save_ctx_ongoing = 1;
  // Wait for hash to be done so the digest is updated.
  csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
  // Clear the interrupt.
  csr_wr(.ptr(ral.intr_state.hmac_done), .value(1'b1));
  // Read the digest and save it.
  csr_rd_digest(digest_a);
  // Read message length and save it.
  csr_rd_msg_length(msg_length_a);
  save_ctx_ongoing = 0;
  // Disable SHA so we can write digest and message length.
  csr_wr(.ptr(ral.cfg.sha_en), .value(1'b0));
  // Clearing the message length is not strictly necessary but currently done to ensure the
  // previous value does not persist.
  csr_wr_msg_length('0); //
  // Reload the digest by writing it back.
  csr_wr_digest(digest_a);
  // Reload the message length by writing it back.
  csr_wr_msg_length(msg_length_a);
  // Re-enable SHA and continue hashing.
  csr_wr(.ptr(ral.cfg.sha_en), .value(1'b1));
  trigger_hash_continue();
  sar_same_ctxt_ev.trigger();
  sar_ongoing = 0;
endtask : sar_same_context;

//   Different context:
//   All those parameters could be changed: key length, digest size, digest swap, endian swap
//   and secret key, update all those registers and restart. Operations:
//      1- config registers for A, run A hash, stop A hash
//      2- save A context
//      3- config registers for B, run hash process/continue, wait B hash completion
//      4- run B hash, stop B hash
//      5- restore A context, resume A hash until the end
//   Note: here we are taking the advantage of SAR feature to test the msg_length_upper register
task hmac_base_vseq::sar_different_context();
  bit [TL_DW-1:0]   digest_a[16];
  bit [2*TL_DW-1:0] msg_length_a;
  bit [7:0]         msg_b[];
  bit [2*TL_DW-1:0] msg_length_rd, msg_length_rand;
  uvm_event         sar_different_ctxt_ev;

  sar_different_ctxt_ev = uvm_event_sar_pool::get_global("sar_different_context_event");
  // ----- 1- config registers for A, run A hash, stop A hash
  `uvm_info(`gfn, $sformatf("Saving and restoring with different contexts"), UVM_LOW)
  sar_ongoing = 1;
  // Stop hash operations.
  trigger_hash_stop();
  // Expose ongoing Save and Restore triggered to avoid to request a new hash process
  save_ctx_ongoing = 1;
  // Wait for hash to be done so the digest is updated.
  csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
  // Clear the interrupt.
  csr_wr(.ptr(ral.intr_state.hmac_done), .value(1'b1));

  // ----- 2- save A context
  // Read the digest and save it.
  csr_rd_digest(digest_a);
  // Read message length and save it.
  csr_rd_msg_length(msg_length_a);
  save_ctx_ongoing = 0;

  // ----- 3- config registers for B, run hash process/continue, wait B hash completion
  // Disable SHA so we can write digest and message length.
  csr_wr(.ptr(ral.cfg.sha_en), .value(1'b0));
  // Generate random message for B context
  msg_b = new[$urandom_range(0, 400)];
  foreach (msg_b[i]) msg_b[i] = $urandom();
  `uvm_info(`gfn, $sformatf("SAR context B - message size %0d bits", msg_b.size()*8), UVM_LOW)
  `uvm_info(`gfn, $sformatf("SAR context B - msg_b=%p", msg_b), UVM_LOW)
  // Set this flag to tell the SCB to skip ongoing things
  cfg.sar_skip_ctxt = 1;
  // Save config A, generate config B and config DUT
  save_and_restore_cfg(1, 0);
  // In 50% of the case run a new context from the beginning, or restore a hypothetical context
  // with a huge message length to test the upper part of the register msg_length_upper
  randcase
    1:  begin
          // Re-enable SHA and continue hashing.
          csr_wr(.ptr(ral.cfg.sha_en), .value(1'b1));
          // Start processing message stream
          trigger_hash();
          // Write complete message for B context
          wr_msg(msg_b, 1);
          // Start hash
          trigger_process();
          // Wait for hash to be done so the digest is updated.
          csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
        end
    1:  begin
          // Override the msg_length value to be able to verify the upper part of the register.
          // We need to cover the 32 MSBs of this register. Be careful, the programmed value
          // has to be a multiple of 512/1024 otherwise the DUT won't support it!
          randcase
            1: msg_length_rand = 'h0000_0000_FFFF_FC00;   // Toggle LSB upper part reg transition
            1: msg_length_rand = 'hFFFF_FFFF_FFFF_A800;   // Toggle MSB, without overflowing
          endcase
          csr_wr_msg_length(msg_length_rand);
          // Re-enable SHA and continue hashing.
          csr_wr(.ptr(ral.cfg.sha_en), .value(1'b1));
          // Trigger hash to continue
          trigger_hash_continue();
          // Write complete message for B context
          wr_msg(msg_b, 1);
          // Start hash
          trigger_process();
          // Wait for hash to be done so the digest is updated.
          csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
          // Check message length -> TODO (#23562) move to the SCB when removing sar_skip_ctxt
          csr_rd_msg_length(msg_length_rd);
          `DV_CHECK_EQ(msg_length_rd, msg_length_rand+msg_b.size()*8)
        end
  endcase
  // Clear the interrupt.
  csr_wr(.ptr(ral.intr_state.hmac_done), .value(1'b1));
  // Clear this flag to tell the SCB to proceed with the prediction and checks
  cfg.sar_skip_ctxt = 0;
  save_ctx_ongoing  = 0;

  // ----- 4- restore A context, resume A hash until the end
  // Disable SHA so we can write digest and message length.
  csr_wr(.ptr(ral.cfg.sha_en), .value(1'b0));
  // Restore config A without saving config B as not required
  save_and_restore_cfg(0, 1);
  // Reload the digest by writing it back.
  csr_wr_digest(digest_a);
  // Reload the message length by writing it back.
  csr_wr_msg_length(msg_length_a);
  // Re-enable SHA and continue hashing.
  csr_wr(.ptr(ral.cfg.sha_en), .value(1'b1));
  trigger_hash_continue();
  sar_different_ctxt_ev.trigger();
  sar_ongoing = 0;
endtask : sar_different_context;

// Save the current config for some registers, and restore the previous saved config or genrate
// a new random one
task hmac_base_vseq::save_and_restore_cfg(bit save_current_cfg, bit restore_previous_cfg);
  hmac_base_vseq  rand_cfg;     // Only here to randomize variables
  bit             endian_swap_tmp;
  bit             digest_swap_tmp;
  bit             key_swap_tmp;
  bit [3:0]       digest_size_tmp;
  bit [5:0]       key_length_tmp;
  bit [TL_DW-1:0] key_tmp[];
  string          secret_key_path = {`DUT_HIER_STR, ".secret_key"};
  logic [NUM_KEYS*TL_DW-1:0] secret_key_probe;

  `DV_CHECK_FATAL(uvm_hdl_read(secret_key_path, secret_key_probe),
                  $sformatf("Failed to access path %s", secret_key_path))

  if (save_current_cfg) begin
    endian_swap_tmp = `gmv(ral.cfg.endian_swap);
    digest_swap_tmp = `gmv(ral.cfg.digest_swap);
    key_swap_tmp    = `gmv(ral.cfg.key_swap);
    digest_size_tmp = `gmv(ral.cfg.digest_size);
    key_length_tmp  = `gmv(ral.cfg.key_length);
    key_tmp         = new[get_key_length(key_length_tmp)/TL_DW];
    for (int i=0; i<key_tmp.size(); i++) begin
      key_tmp[i] = secret_key_probe[NUM_KEYS*TL_DW-i*TL_DW-1 -: TL_DW];
    end
    // As the probed secret key from the HDL is already swapped, a swap back to the original
    // value has to be performed
    if (key_swap_tmp) begin
      foreach (key_tmp[key_i]) begin
        key_tmp[key_i] = {<<8{key_tmp[key_i]}};
      end
    end
  end

  // Restore the previous config
  if (restore_previous_cfg) begin
    ral.cfg.endian_swap.set(endian_swap_bak);
    ral.cfg.digest_swap.set(digest_swap_bak);
    ral.cfg.key_swap.set(key_swap_bak);
    ral.cfg.digest_size.set(digest_size_bak);
    ral.cfg.key_length.set(key_length_bak);
    csr_update(.csr(ral.cfg));
    wr_key(key_bak);
  // Generate new randomized config with the current set of constraints
  end else begin
    rand_cfg = hmac_base_vseq::type_id::create("rand_cfg");
    rand_cfg.set_sequencer(p_sequencer);  // Won't be used but needed to avoid error
    // Randomize valid configuration only
    `DV_CHECK_FATAL(rand_cfg.randomize() with {
      solve digest_size before key_length;
      $countones(digest_size) == 1;
      $countones(key_length)  == 1;
      digest_size != SHA2_None;
      (local::hmac_en) -> (key_length != Key_None);
      (local::hmac_en && digest_size == SHA2_256) -> (key_length != Key_1024);
    })
    // Write into registers
    ral.cfg.endian_swap.set(rand_cfg.endian_swap);
    ral.cfg.digest_swap.set(rand_cfg.digest_swap);
    ral.cfg.key_swap.set(rand_cfg.key_swap);
    ral.cfg.digest_size.set(rand_cfg.digest_size);
    ral.cfg.key_length.set(rand_cfg.key_length);
    csr_update(.csr(ral.cfg));
    wr_key(rand_cfg.key);
    `uvm_info(`gfn, $sformatf("SAR context B - digest size=%s, key length=%0d",
              get_digest_size(rand_cfg.digest_size),
              get_key_length(rand_cfg.key_length)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("SAR context B - endian/digest/key_swap=%b",
              {rand_cfg.endian_swap, rand_cfg.digest_swap, rand_cfg.key_swap}), UVM_LOW)
    `uvm_info(`gfn, $sformatf("SAR context B - key=%p", rand_cfg.key), UVM_LOW)
  end

  // Copy over into the previous config variables
  endian_swap_bak = endian_swap_tmp;
  digest_swap_bak = digest_swap_tmp;
  key_swap_bak    = key_swap_tmp;
  digest_size_bak = digest_size_tmp;
  key_length_bak  = key_length_tmp;
  key_bak         = key_tmp;
endtask : save_and_restore_cfg

// Overriding timeout on outstanding accesses for the hmac_stress_test_all_with_rand_reset test
function int hmac_base_vseq::wait_cycles_with_no_outstanding_accesses();
  return 1_000_000;
endfunction : wait_cycles_with_no_outstanding_accesses
