// Copyright lowRISC contributors.
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
  rand bit [TL_AW-1:0]  wr_addr;
  rand bit [TL_DBW-1:0] wr_mask;
  rand bit wr_config_during_hash, wr_key_during_hash;

  constraint wr_addr_c {
    wr_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]};
  }

  constraint wr_mask_c {
    $countones(wr_mask) dist {
        TL_DBW       :/ 1,
        [1:TL_DBW-1] :/ 1
    };
  }

  constraint wr_mask_contiguous_c {
    $countones(wr_mask ^ {wr_mask[TL_DBW-2:0], 1'b0}) <= 2; // mask must have continues ones
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if (do_hmac_init) hmac_init();
  endtask

  virtual task dut_shutdown();
    super.dut_shutdown();
    // TODO: nothing extra to do yet
  endtask

  virtual task hmac_init(bit sha_en = 1'b1,
                         bit hmac_en = 1'b1,
                         bit endian_swap = 1'b1,
                         bit digest_swap = 1'b1,
                         bit intr_fifo_empty_en = 1'b1,
                         bit intr_hmac_done_en = 1'b1,
                         bit intr_hmac_err_en  = 1'b1);
    bit [TL_DW-1:0] interrupts;
    // enable sha, hmac data paths and writing to msg_fifo
    ral.cfg.sha_en.set(sha_en);
    ral.cfg.hmac_en.set(hmac_en);
    ral.cfg.endian_swap.set(endian_swap);
    ral.cfg.digest_swap.set(digest_swap);
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
    randcase
      1:  csr_wr(ral.key_0, rand_key_value);
      1:  csr_wr(ral.key_1, rand_key_value);
      1:  csr_wr(ral.key_2, rand_key_value);
      1:  csr_wr(ral.key_3, rand_key_value);
      1:  csr_wr(ral.key_4, rand_key_value);
      1:  csr_wr(ral.key_5, rand_key_value);
      1:  csr_wr(ral.key_6, rand_key_value);
      1:  csr_wr(ral.key_7, rand_key_value);
    endcase
  endtask

  // trigger hash computation to start
  virtual task trigger_hash();
    csr_wr(.csr(ral.cmd), .value(1'b1 << HashStart));
    // if sha is not enabled, assert error interrupt and check error code
    if (!ral.cfg.sha_en.get_mirrored_value()) check_error_code();
  endtask

  virtual task trigger_process();
    csr_wr(.csr(ral.cmd), .value(1'b1 << HashProcess));
  endtask

  virtual task trigger_hash_when_active();
    repeat ($urandom_range(1, 10)) trigger_hash();
    check_error_code(0);
  endtask

  // read digest value
  virtual task rd_digest();
    bit [TL_DW-1:0] digest[8];
    csr_rd_digest(digest);
  endtask

    // read digest value and output read value
  virtual task csr_rd_digest(output bit [TL_DW-1:0] digest[8]);
    csr_rd(.ptr(ral.digest_0), .value(digest[0]));
    csr_rd(.ptr(ral.digest_1), .value(digest[1]));
    csr_rd(.ptr(ral.digest_2), .value(digest[2]));
    csr_rd(.ptr(ral.digest_3), .value(digest[3]));
    csr_rd(.ptr(ral.digest_4), .value(digest[4]));
    csr_rd(.ptr(ral.digest_5), .value(digest[5]));
    csr_rd(.ptr(ral.digest_6), .value(digest[6]));
    csr_rd(.ptr(ral.digest_7), .value(digest[7]));
  endtask

  // write 256-bit hashed key
  //
  // can safely assume that the input array will always have 8 elements
  // since HMAC key size is always 256 bits
  virtual task wr_key(bit [TL_DW-1:0] key[]);
    // pity we cant loop here
    ral.key_0.set(key[0]);
    ral.key_1.set(key[1]);
    ral.key_2.set(key[2]);
    ral.key_3.set(key[3]);
    ral.key_4.set(key[4]);
    ral.key_5.set(key[5]);
    ral.key_6.set(key[6]);
    ral.key_7.set(key[7]);
    csr_update(.csr(ral.key_0));
    csr_update(.csr(ral.key_1));
    csr_update(.csr(ral.key_2));
    csr_update(.csr(ral.key_3));
    csr_update(.csr(ral.key_4));
    csr_update(.csr(ral.key_5));
    csr_update(.csr(ral.key_6));
    csr_update(.csr(ral.key_7));
    foreach (key[i]) begin
      `uvm_info(`gfn, $sformatf("key[%0d] = 0x%0h", i, key[i]), UVM_HIGH)
    end
  endtask

  // write msg to DUT, read status FIFO FULL and check intr FIFO FULL
  virtual task wr_msg(bit [7:0] msg[], bit non_blocking = $urandom_range(0, 1));
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
                                wr_addr, wr_mask, word), UVM_HIGH)
      tl_access(.addr(cfg.ral.get_addr_from_offset(wr_addr)),
                .write(1'b1), .data(word), .mask(wr_mask), .blocking(non_blocking));

      if (ral.cfg.sha_en.get_mirrored_value()) begin
        if (!do_back_pressure) begin
          if ($urandom_range(0, 1)) check_status_intr();
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
    check_status_intr();
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
        if (ral.cfg.sha_en.get_mirrored_value()) begin
          //clear_intr_fifo_full();
        end else begin
          check_error_code();
        end
      end else begin // remaining msg is smaller than the burst_wr_length
        wr_msg(msg_q);
        break;
      end
    csr_utils_pkg::wait_no_outstanding_access();
    if ($urandom_range(0, 1)) rd_msg_length();
    end
  endtask

  // read the message length from the DUT reg
  virtual task rd_msg_length();
    bit [TL_DW-1:0] length_upper, length_lower;
    csr_rd(ral.msg_length_upper, length_upper);
    csr_rd(ral.msg_length_lower, length_lower);
  endtask

  // read status FIFO FULL and check intr FIFO FULL
  // if intr_fifo_full_enable is disable, check intr_fifo_full_state and clear it
  virtual task check_status_intr();
    bit [TL_DW-1:0] rdata;
    csr_utils_pkg::wait_no_outstanding_access();
    csr_rd(ral.status, rdata);
    csr_rd(ral.intr_state, rdata);
    csr_wr(.csr(ral.intr_state), .value(rdata));
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
        csr_wr(.csr(ral.intr_state), .value(1 << HmacErr));
      end
    end else begin
      csr_rd(.ptr(ral.intr_state), .value(error_code));
      csr_wr(.csr(ral.intr_state), .value(error_code));
    end
    csr_rd(ral.err_code, error_code);
  endtask

  virtual task compare_digest(bit [7:0] exp_digest[]);
    bit [TL_DW-1:0] act_digest[8];
    bit [TL_DW-1:0] packed_exp_digest[8];
    csr_rd_digest(act_digest);
    // `exp_digest` is guaranteed to always contain 32 bytes of data since
    // HMAC digest size is always 256 bits.
    packed_exp_digest = {>>byte{exp_digest}};
    if (cfg.clk_rst_vif.rst_n) begin
      // can safely assume that `exp_digest` always has 8 elements
      // since HMAC output size is 256 bits.
      foreach (act_digest[i]) begin
        `DV_CHECK_EQ(act_digest[i], packed_exp_digest[i],
                     $sformatf("for index %0d", i))
      end
    end else begin
      `uvm_info(`gfn, "skipped comparison due to reset", UVM_LOW)
    end
  endtask

endclass : hmac_base_vseq
