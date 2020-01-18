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
  rand bit [TL_SZW-1:0] wr_size;
  rand bit [TL_DBW-1:0] wr_mask;

  //TODO: temp constraints here, eventually should move to TL_ACCESS
  constraint wr_size_c {
    wr_size inside {[0:2]}; // 0 is 2**0 byte size
  }

  constraint wr_addr_c {
    wr_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]};
    wr_addr << (TL_AW - wr_size) == 0;
  }

  constraint wr_mask_align_with_addr_c {
    if (wr_addr[1:0] == 1) {
      wr_mask[0] == 0;
    } else if (wr_addr[1:0] == 2) {
      wr_mask[1:0] == 0;
    } else if (wr_addr[1:0] == 3) {
      wr_mask[2:0] == 0;
    }
  }

  constraint wr_mask_c {
    $countones(wr_mask) dist {
        TL_DBW       :/ 1,
        [1:TL_DBW-1] :/ 1
    };
  }

  constraint wr_mask_size_c {
    $countones(wr_mask) <= ('b1 << wr_size);
  }

  constraint wr_mask_conintuous_c {
    $countones(wr_mask ^ {wr_mask[TL_DBW-2:0], 1'b0}) <= 2; // mask must have continues ones
  }

  // mask must be within enabled lanes
  // prevent cases: addr: 0h, size: 1, mask: 'b1100; addr: 0h, size: 0, mask: 'b1000
  constraint mask_in_enabled_lanes_c {
    ((wr_mask >> wr_addr[1:0]) >> (1 << wr_size)) == 0;
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    alert_send_ping();
    if (do_hmac_init) hmac_init();
  endtask

  virtual task alert_send_ping();
    alert_receiver_seq ping_seq;
    `uvm_create_on(ping_seq, p_sequencer.alert_esc_sequencer_h[cfg.list_of_alerts[0]]);
    `DV_CHECK_RANDOMIZE_FATAL(ping_seq)
    `uvm_send(ping_seq)
  endtask

  virtual task dut_shutdown();
    super.dut_shutdown();
    // TODO: nothing extra to do yet
  endtask

  virtual task hmac_init(bit sha_en = 1'b1,
                         bit hmac_en = 1'b1,
                         bit endian_swap = 1'b1,
                         bit digest_swap = 1'b1,
                         bit intr_fifo_full_en = 1'b1,
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
                 (intr_fifo_full_en << HmacMsgFifoFull);
    cfg_interrupts(.interrupts(interrupts), .enable(1'b1));
  endtask

  virtual task write_discard_config_and_key(bit do_wr_config, bit do_wr_key);
    if (do_wr_config) write_discard_config();
    if (do_wr_key) begin
      write_discard_key();
      check_error_code();
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
      1:  csr_wr(ral.key0, rand_key_value);
      1:  csr_wr(ral.key1, rand_key_value);
      1:  csr_wr(ral.key2, rand_key_value);
      1:  csr_wr(ral.key3, rand_key_value);
      1:  csr_wr(ral.key4, rand_key_value);
      1:  csr_wr(ral.key5, rand_key_value);
      1:  csr_wr(ral.key6, rand_key_value);
      1:  csr_wr(ral.key7, rand_key_value);
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

  // read digest value
  virtual task rd_digest();
    logic [TL_DW-1:0] digest[8];
    csr_rd_digest(digest);
  endtask

    // read digest value and output read value
  virtual task csr_rd_digest(output bit [TL_DW-1:0] digest[8]);
    csr_rd(.ptr(ral.digest0), .value(digest[0]));
    csr_rd(.ptr(ral.digest1), .value(digest[1]));
    csr_rd(.ptr(ral.digest2), .value(digest[2]));
    csr_rd(.ptr(ral.digest3), .value(digest[3]));
    csr_rd(.ptr(ral.digest4), .value(digest[4]));
    csr_rd(.ptr(ral.digest5), .value(digest[5]));
    csr_rd(.ptr(ral.digest6), .value(digest[6]));
    csr_rd(.ptr(ral.digest7), .value(digest[7]));
  endtask

  // write 256-bit hashed key
  virtual task wr_key(bit [TL_DW-1:0] key[8]);
    // pity we cant loop here
    ral.key0.set(key[0]);
    ral.key1.set(key[1]);
    ral.key2.set(key[2]);
    ral.key3.set(key[3]);
    ral.key4.set(key[4]);
    ral.key5.set(key[5]);
    ral.key6.set(key[6]);
    ral.key7.set(key[7]);
    csr_update(.csr(ral.key0));
    csr_update(.csr(ral.key1));
    csr_update(.csr(ral.key2));
    csr_update(.csr(ral.key3));
    csr_update(.csr(ral.key4));
    csr_update(.csr(ral.key5));
    csr_update(.csr(ral.key6));
    csr_update(.csr(ral.key7));
    foreach (key[i]) begin
      `uvm_info(`gfn, $sformatf("key[%0d] = 0x%0h", i, key[i]), UVM_HIGH)
    end
  endtask

  // write msg to DUT, read status FIFO FULL and check intr FIFO FULL
  virtual task wr_msg(bit [7:0] msg[]);
    bit [7:0] msg_q[$] = msg;

    // randomly pick the size of bytes to write
    // unless msg size is smaller than randomized size
    while (msg_q.size() > 0) begin
      bit [7:0] word_unpack[4];
      bit [TL_DW-1:0] word;

      if (!do_back_pressure && ral.cfg.sha_en.get_mirrored_value()) begin
        // if not back pressure sequence, wait until fifo_full status cleared then write
        bit msg_fifo_full;
        csr_rd(ral.status.fifo_full, msg_fifo_full);
        if (msg_fifo_full) csr_spinwait(.ptr(ral.status.fifo_full), .exp_data(1'b0));
      end

      if (msg_q.size() < 4) begin
        `DV_CHECK_FATAL(randomize(wr_size, wr_addr, wr_mask)
                        with {1 << wr_size <= msg_q.size();})
      end else begin
        `DV_CHECK_FATAL(randomize(wr_size, wr_addr, wr_mask));
      end
      foreach (wr_mask[i]) begin
        // wr_mask is a packed array, word_unpacked is unpack, has different index
        if (wr_mask[i]) word_unpack[3 - i] = msg_q.pop_front();
        else word_unpack[3 - i] = $urandom();
      end
      word = {>>byte{word_unpack}};
      `uvm_info(`gfn, $sformatf("wr_size = %0h, wr_addr = %0h, wr_mask = %0h, words = 0x%0h",
                                wr_size, wr_addr, wr_mask, word), UVM_HIGH)
      tl_access(.addr(wr_addr), .write(1'b1), .data(word), .mask(wr_mask), .size(wr_size),
                .blocking($urandom_range(0, 1)));

      if (ral.cfg.sha_en.get_mirrored_value()) begin
        if (!do_back_pressure) check_status_intr_fifo_full();
        else clear_intr_fifo_full();
        // randomly change key, config regs during msg wr, should trigger error or be discarded
        write_discard_config_and_key($urandom_range(0, 20) == 0, $urandom_range(0, 20) == 0);
      end else begin
        check_error_code();
      end
    end
    // ensure all msg fifo are written before trigger hmac_process
    csr_utils_pkg::wait_no_outstanding_access();
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
          `uvm_info(`gfn, $sformatf("wr_size = %0h, wr_addr = %0h, wr_mask = %0h, words = 0x%0h",
                                    wr_size, wr_addr, wr_mask, word), UVM_HIGH)
          `DV_CHECK_FATAL(randomize(wr_size, wr_addr, wr_mask) with {wr_size == 2;})
          tl_access(.addr(wr_addr), .write(1'b1), .data(word), .mask(wr_mask), .size(wr_size),
                    .blocking($urandom_range(0, 1)));
        end
        if (ral.cfg.sha_en.get_mirrored_value()) begin
          clear_intr_fifo_full();
        end else begin
          check_error_code();
        end
      end else begin // remaining msg is smaller than the burst_wr_length
        wr_msg(msg_q);
        break;
      end
    csr_utils_pkg::wait_no_outstanding_access();
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
  virtual task check_status_intr_fifo_full();
    bit msg_fifo_full;
    csr_utils_pkg::wait_no_outstanding_access();
    csr_rd(ral.status.fifo_full, msg_fifo_full);
    if (ral.intr_enable.fifo_full.get_mirrored_value()) begin
      check_interrupts(.interrupts((1 << HmacMsgFifoFull)), .check_set(msg_fifo_full));
    end else begin
      csr_rd_check(.ptr(ral.intr_state), .compare_value(msg_fifo_full),
                   .compare_mask(1 << HmacMsgFifoFull));
      csr_wr(.csr(ral.intr_state), .value(msg_fifo_full << HmacMsgFifoFull));
    end
  endtask

  // when msg fifo full interrupt is set, this task clears the interrupt
  // checking the correctness of the fifo full interrupt is done in scb
  virtual task clear_intr_fifo_full();
    csr_utils_pkg::wait_no_outstanding_access();
    if (ral.intr_enable.fifo_full.get_mirrored_value()) begin
      if (cfg.intr_vif.pins[HmacMsgFifoFull] === 1'b1) begin
        check_interrupts(.interrupts((1 << HmacMsgFifoFull)), .check_set(1'b1));
      end
    end else begin
      bit msg_fifo_full;
      csr_rd(ral.intr_state.fifo_full, msg_fifo_full);
      if (msg_fifo_full) csr_wr(.csr(ral.intr_state), .value(msg_fifo_full << HmacMsgFifoFull));
    end
  endtask

  // this task is called when sha_en=0 and sequence set hash_start, or streamed in msg
  // it will check intr_pin, intr_state, and error_code register
  virtual task check_error_code();
    bit [TL_DW-1:0] error_code;
    csr_utils_pkg::wait_no_outstanding_access();
    if (ral.intr_enable.hmac_err.get_mirrored_value()) begin
      check_interrupts(.interrupts((1 << HmacErr)), .check_set(1'b1));
    end else begin
      csr_rd_check(.ptr(ral.intr_state), .compare_value(1 << HmacErr));
      csr_wr(.csr(ral.intr_state), .value(1 << HmacErr));
    end
    csr_rd(ral.err_code, error_code);
  endtask

  virtual task compare_digest(bit [TL_DW-1:0] exp_digest[8]);
    logic [TL_DW-1:0] act_digest[8];
    csr_rd_digest(act_digest);
    if (cfg.clk_rst_vif.rst_n) begin
      foreach (act_digest[i]) begin
        `DV_CHECK_EQ(act_digest[i], exp_digest[i], $sformatf("for index %0d", i))
      end
    end else begin
      `uvm_info(`gfn, "skipped comparison due to reset", UVM_LOW)
    end
  endtask

endclass : hmac_base_vseq
