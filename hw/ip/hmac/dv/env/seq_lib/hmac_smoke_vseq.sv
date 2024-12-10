// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_smoke_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_smoke_vseq)

  rand bit               sha_en;
  rand bit               intr_fifo_empty_en;
  rand bit               intr_hmac_done_en;
  rand bit               intr_hmac_err_en;
  rand bit [7:0]         msg[];
  rand int               burst_wr_length;
  rand bit               do_hash_start_when_active;
  rand bit               do_hash_start;
  rand bit               re_enable_sha;
  rand wipe_secret_req_e do_wipe_secret;

  int key_process_cycles;

  // Constraints
  extern constraint num_trans_c;
  extern constraint legal_seq_c;
  extern constraint msg_c;
  extern constraint burst_wr_c;
  extern constraint intr_enable_c;
  extern constraint wipe_secret_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern virtual task pre_start();
  extern task body();
endclass: hmac_smoke_vseq


constraint hmac_smoke_vseq::num_trans_c {
  num_trans inside {[1:50]};
}

constraint hmac_smoke_vseq::legal_seq_c {
  do_hash_start             == 1;
  sha_en                    == 1;
  do_hash_start_when_active == 0;
  wr_key_during_hash        == 0;
  wr_config_during_hash     == 0;
}

//msg[] is a streaming msg input so can be of any size and needs its size dist-constrained
constraint hmac_smoke_vseq::msg_c {
  msg.size() dist {
    0         :/ 3,   // Empty
    [  1: 62] :/ 1,   // Less than a SHA-2 256 block (512-bit)
    [ 63: 65] :/ 3,   // Around one SHA-2 256 block (512-bit)
    [ 66:126] :/ 1,   // Less than a SHA-2 384/512 block (1024-bit) or two 512-bit blocks
    [127:129] :/ 3,   // Around one SHA-2 384/512 block (1024-bit) or two 512-bit blocks
    [130:254] :/ 1,   // Less than two 1024-bit blocks
    [255:257] :/ 3    // Around two 1024-bit blocks
  };
}

constraint hmac_smoke_vseq::burst_wr_c {
  burst_wr_length inside {[1 : HMAC_MSG_FIFO_DEPTH_WR]};
}

constraint hmac_smoke_vseq::intr_enable_c {
  intr_fifo_empty_en dist {
    1'b1 := 8,
    1'b0 := 2
  };
  intr_hmac_done_en dist {
    1'b1 := 8,
    1'b0 := 2
  };
  intr_hmac_err_en dist {
    1'b1 := 8,
    1'b0 := 2
  };
}

constraint hmac_smoke_vseq::wipe_secret_c {
  do_wipe_secret == NoWipeSecret;
}

function hmac_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_smoke_vseq::pre_start();
  do_hmac_init = 1'b0;
  super.pre_start();
endtask : pre_start

task hmac_smoke_vseq::body();
  for (int i = 1; i <= num_trans; i++) begin
    bit [7:0] msg_q[$];
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, message size %0d bits, hmac=%0d, sha=%0d",
              i, num_trans, msg.size()*8, hmac_en, sha_en), UVM_LOW)
    `uvm_info(`gfn, $sformatf("digest size=%s, key length=%0d",
              get_digest_size(digest_size), get_key_length(key_length)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("intr_fifo_empty/hmac_done/hmac_err=%b, endian/digest/key_swap=%b",
              {intr_fifo_empty_en, intr_hmac_done_en, intr_hmac_err_en},
              {endian_swap, digest_swap, key_swap}), UVM_LOW)
    `uvm_info(`gfn, $sformatf("wipe secret condition is: %0s", do_wipe_secret.name()), UVM_LOW)

    // initialize hmac configs
    hmac_init(.sha_en(sha_en), .hmac_en(hmac_en), .endian_swap(endian_swap),
              .digest_swap(digest_swap), .key_swap(key_swap), .digest_size(digest_size),
              .key_length(key_length), .intr_fifo_empty_en(intr_fifo_empty_en),
              .intr_hmac_done_en(intr_hmac_done_en), .intr_hmac_err_en(intr_hmac_err_en));

    // always start off the transaction by first clearing cfg.wipe_secret_triggered flag
    // and update the exp digest val in scb with last digest
    clear_wipe_secret();
    rd_digest();

    if (do_wipe_secret == WipeSecretBeforeKey) begin
      `uvm_info(`gfn, $sformatf("wiping before key"), UVM_HIGH)
      wipe_secrets();
      // Check if digest data are corrupted by wiping secrets.
      rd_digest();
    end

    // write key
    wr_key(key);

    // clear the flag after writing key
    clear_wipe_secret();

    // randomly read previous digest, if the previous digest is not corrupted by wipe_secret
    if (i != 1 && $urandom_range(0, 1)) begin
      rd_digest();
    end

    if (do_wipe_secret == WipeSecretBeforeStart) begin
      `uvm_info(`gfn, $sformatf("wiping before start"), UVM_HIGH)
      wipe_secrets();
      // Here the wipe secret will only corrupt secret keys and current digests.
      // If HMAC is not enabled, once we trigger start, the corruption does not affect the digest
      // that will get computed. If HMAC is enabled, the key got corrupted, so the digest
      // that will get computed will be corrupted, so only call clear_wipe_secret() when !hmac_en.
      if (!hmac_en) begin
        // read corrupted current digests then...
        rd_digest();
        // clear the flag at/right before starting
        clear_wipe_secret();
      end
    end

    if (sha_en || $urandom_range(0, 1)) begin
      bit [TL_DW-1:0] intr_state_val;
      // start stream in msg
      fork
        begin
          if (do_hash_start) begin
            trigger_hash();
          end
          if (do_burst_wr) begin
            burst_wr_msg(msg, burst_wr_length);
          end else begin
            wr_msg(msg);
          end
        end

        begin
          if (do_wipe_secret == WipeSecretBeforeProcess) begin
            `uvm_info(`gfn, $sformatf("wiping before process"), UVM_HIGH)
            cfg.clk_rst_vif.wait_clks($urandom_range(0, msg.size() * 10));
            wipe_secrets();
          end
        end
      join

      if (invalid_cfg) begin
        rd_digest(); // capture the digest CSRs before moving on to next transaction
        continue; // discard current transaction
      end else if (!sha_en) begin
        if (re_enable_sha) begin // restream in the message
          sha_enable();
          if (do_hash_start) begin
            trigger_hash();
          end
          wr_msg(msg);
        end else begin // discard current transaction
          continue;
        end
      end

      if (do_hash_start_when_active && do_hash_start) begin
        trigger_hash_when_active();
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(msg)
        wr_msg(msg);
      end

      // msg stream in finished, start hash
      if (do_hash_start) begin
        `uvm_info(`gfn, $sformatf("triggering process because msg stream is finished"), UVM_LOW)
        trigger_process();
      end

      // there is one clk cycle difference between scb and design when predict fifo_empty,
      // it could happen when input message length is not a multiple of 4, then in design
      // the `sha2_pad.st_q` will transit from `StFifoReceive` to `StPad80`.
      // If the last two fifo_rds are back-to-back, then design will have one cycle delay before
      // the last fifo_rd in order to switch the state.
      // If the last two fifo_rds are not back-to-back, then there won't be any delay for the
      // last fifo_rd.
      // the wait_clk below is implemented to avoid checking intr_state during this period of time
      // for such corner cases, because it is hard to align the scb with the fifo_empty interrupt.
      // Since prim_packer can hold more data, the ignored period of time is extended by * 2.
      if (`gmv(ral.cfg.digest_size) == SHA2_256) begin
        key_process_cycles = HMAC_KEY_PROCESS_CYCLES_256;
      end else begin
        key_process_cycles = HMAC_KEY_PROCESS_CYCLES_512;
      end
      cfg.clk_rst_vif.wait_clks((msg.size() % 4 || !legal_seq_c.constraint_mode()) ?
                                key_process_cycles * 2 :
                                $urandom_range(0, key_process_cycles * 2));

      if (do_hash_start) begin
        fork
          begin
            if (!invalid_cfg) begin
              // wait for interrupt to assert, check status and clear it
              if (intr_hmac_done_en) begin
                `DV_WAIT(cfg.intr_vif.pins[HmacDone] === 1'b1)
              end else begin
                csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
              end
            end
          end
          begin
            if (do_wipe_secret == WipeSecretBeforeDone) begin
              `uvm_info(`gfn, $sformatf("wiping before done"), UVM_HIGH)
              cfg.clk_rst_vif.wait_clks($urandom_range(0, 100));
              wipe_secrets();
            end
          end
        join
      end
      csr_rd(.ptr(ral.intr_state), .value(intr_state_val));
      csr_wr(.ptr(ral.intr_state), .value(intr_state_val));
    end

    // if disable sha, digest should be cleared
    // read msg fifo length
    if ($urandom_range(0, 1)) begin
      rd_msg_length();
    end

    // read digest from DUT
    `uvm_info(`gfn, $sformatf("reading digest"), UVM_LOW)
    rd_digest();
  end
endtask : body
