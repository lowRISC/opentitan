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

  constraint wr_size_c {
    wr_size inside {[0:2]}; // 0 is 2**0 byte size
  }

  constraint wr_addr_c {
    wr_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]};
    wr_addr << (TL_AW - wr_size) == 0;
    solve wr_size before wr_addr;
  }

  constraint wr_mask_c {
    $countones(wr_mask) == (1 << wr_size);
    (wr_addr & 'b01) -> wr_mask[0] == 0;
    (wr_addr & 'b10) -> wr_mask[1:0] == 0;
    (wr_addr & 'b11) -> wr_mask[2:0] == 0;
    !(wr_mask inside {'h5, 'h9, 'ha, 'hb, 'hd}); // mask must have continues ones
    solve wr_size before wr_mask;
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
                         bit digest_swap = 1'b1);
    bit [TL_DW-1:0] interrupts;
    // enable sha, hmac data paths and writing to msg_fifo
    ral.cfg.sha_en.set(sha_en);
    ral.cfg.hmac_en.set(hmac_en);
    ral.cfg.endian_swap.set(endian_swap);
    ral.cfg.digest_swap.set(digest_swap);
    csr_update(.csr(ral.cfg));

    // enable interrupts
    interrupts = (1 << HmacDone) | (1 << HmacMsgFifoFull);
    cfg_interrupts(.interrupts(interrupts), .enable(1'b1));
  endtask

  // trigger hash computation to start
  virtual task trigger_hash();
    csr_wr(.csr(ral.cmd), .value(1'b1));
  endtask

  virtual task trigger_process();
    csr_wr(.csr(ral.cmd), .value(2'b10));
  endtask

  // read digest value
  virtual task rd_digest();
    logic [31:0] digest[8];
    csr_rd_digest(digest);
  endtask

    // read digest value and output read value
  virtual task csr_rd_digest(output bit [31:0] digest[8]);
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
  virtual task wr_key(bit [31:0] key[8]);
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

      if (!do_back_pressure) begin
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
      tl_access(.addr(wr_addr), .write(1'b1), .data(word), .mask(wr_mask), .size(wr_size));

      if (!do_back_pressure) check_status_intr_fifo_full();
      else clear_intr_fifo_full();
    end
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
          tl_access(.addr(wr_addr), .write(1'b1), .data(word), .mask(wr_mask), .size(wr_size));
        end
        clear_intr_fifo_full();
     end else begin // remaining msg is smaller than the burst_wr_length
       wr_msg(msg_q);
       break;
     end
    end
  endtask

  // read the message length from the DUT reg
  virtual task rd_msg_length();
    bit [TL_DW-1:0] length_upper, length_lower;
    csr_rd(ral.msg_length_upper, length_upper);
    csr_rd(ral.msg_length_lower, length_lower);
  endtask

  // read status FIFO FULL and check intr FIFO FULL
  virtual task check_status_intr_fifo_full();
    bit msg_fifo_full;
    csr_rd(ral.status.fifo_full, msg_fifo_full);
    check_interrupts(.interrupts((1 << HmacMsgFifoFull)),
                     .check_set (msg_fifo_full &
                                 ral.intr_enable.fifo_full.get_mirrored_value()));
  endtask

  // when msg fifo full interrupt is set, this task clears the interrupt
  // checking the correctness of the fifo full interrupt is done in scb
  virtual task clear_intr_fifo_full();
    if (cfg.intr_vif.pins[HmacMsgFifoFull] === 1'b1) begin
      check_interrupts(.interrupts((1 << HmacMsgFifoFull)),
                       .check_set (ral.intr_enable.fifo_full.get_mirrored_value()));
    end
  endtask

  virtual task compare_digest(bit [31:0] exp_digest[8]);
    logic [31:0] act_digest[8];
    csr_rd_digest(act_digest);
    foreach (act_digest[i]) begin
      `DV_CHECK_EQ(act_digest[i], exp_digest[i], $sformatf("for index %0d", i))
    end
  endtask

endclass : hmac_base_vseq
