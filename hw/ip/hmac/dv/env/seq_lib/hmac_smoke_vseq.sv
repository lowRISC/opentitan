// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_smoke_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_smoke_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:100]};
  }

  rand bit        hmac_en;
  rand bit        sha_en;
  rand bit        endian_swap;
  rand bit        digest_swap;
  rand bit        intr_fifo_empty_en;
  rand bit        intr_hmac_done_en;
  rand bit        intr_hmac_err_en;
  rand bit [31:0] key[];
  rand bit [7:0]  msg[];
  rand int        burst_wr_length;
  rand bit        do_hash_start_when_active;
  rand bit        do_hash_start;

  // HMAC key size will always be 256 bits.
  constraint key_c {
    key.size() == 8;
  };

  constraint legal_seq_c {
    do_hash_start == 1;
    sha_en == 1;
    do_hash_start_when_active == 0;
    wr_key_during_hash == 0;
    wr_config_during_hash == 0;
  }

  constraint msg_c {
    msg.size() dist {
        0       :/ 1,
        [1 :60] :/ 8,
        [61:64] :/ 1
    }; // upto 64 bytes (16 words, 512 bits)
  }

  constraint burst_wr_c {
    burst_wr_length inside {[1 : HMAC_MSG_FIFO_DEPTH]};
  }

  constraint intr_enable_c {
    intr_fifo_empty_en dist {1'b1 := 8, 1'b0 := 2};
    intr_hmac_done_en dist {1'b1 := 8, 1'b0 := 2};
    intr_hmac_err_en  dist {1'b1 := 8, 1'b0 := 2};
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [7:0] msg_q[$];
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, message size %0d, hmac=%0d, sha=%0d",
                                i, num_trans, msg.size(), hmac_en, sha_en), UVM_LOW)
      `uvm_info(`gfn, $sformatf("intr_fifo_empty/hmac_done/hmac_err_en=%b, endian/digest_swap=%b",
                                {intr_fifo_empty_en, intr_hmac_done_en, intr_hmac_err_en},
                                {endian_swap, digest_swap}), UVM_HIGH)
      // initialize hmac configs
      hmac_init(.sha_en(sha_en), .hmac_en(hmac_en), .endian_swap(endian_swap),
                .digest_swap(digest_swap), .intr_fifo_empty_en(intr_fifo_empty_en),
                .intr_hmac_done_en(intr_hmac_done_en), .intr_hmac_err_en(intr_hmac_err_en));

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      // write key
      wr_key(key);

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      if (sha_en || $urandom_range(0, 1)) begin
        bit [TL_DW-1:0] intr_state_val;
        // start stream in msg
        if (do_hash_start) trigger_hash();

        if (do_burst_wr) burst_wr_msg(msg, burst_wr_length);
        else wr_msg(msg);
        if (!sha_en) begin
          if ($urandom_range(0, 1)) begin // restream in the message
            sha_enable();
            if (do_hash_start) trigger_hash();
            wr_msg(msg);
          end else begin // discard current transaction
            continue;
          end
        end

        if (do_hash_start_when_active && do_hash_start) begin
          trigger_hash_when_active();
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(msg);
          wr_msg(msg);
        end

        // msg stream in finished, start hash
        if (do_hash_start) trigger_process();

        // there is one clk cycle difference between scb and design when predict fifo_empty,
        // it could happen when input message length is not a multiple of 4, then in design
        // the `sha2_pad.st_q` will transit from `StFifoReceive` to `StPad80`.
        // If the last two fifo_rds are back-to-back, then design will have one cycle delay before
        // the last fifo_rd in order to switch the state.
        // If the last two fifo_rds are not back-to-back, then there won't be any delay for the
        // last fifo_rd
        // the wait_clk below is implemented to avoid checking intr_state during this corner case
        cfg.clk_rst_vif.wait_clks((msg.size() % 4 || !legal_seq_c.constraint_mode()) ?
                                  HMAC_KEY_PROCESS_CYCLES * 2 :
                                  $urandom_range(0, HMAC_KEY_PROCESS_CYCLES * 2));

        if (do_hash_start) begin
          // wait for interrupt to assert, check status and clear it
          if (intr_hmac_done_en) begin
            wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
          end else begin
            csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
          end
        end
        csr_rd(.ptr(ral.intr_state), .value(intr_state_val));
        csr_wr(.csr(ral.intr_state), .value(intr_state_val));
      end

      // if disable sha, digest should be cleared
      // read msg fifo length
      if ($urandom_range(0, 1)) rd_msg_length();

      // read digest from DUT
      rd_digest();
    end
  endtask : body

endclass : hmac_smoke_vseq
