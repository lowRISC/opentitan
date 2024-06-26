// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_smoke_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_smoke_vseq)
  `uvm_object_new

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
  bit                    invalid_cfg;
  bit [5:0]              cast_key_length;
  bit [3:0]              cast_digest_size;

  constraint num_trans_c {
    num_trans inside {[1:50]};
  }

  constraint legal_seq_c {
    do_hash_start             == 1;
    sha_en                    == 1;
    do_hash_start_when_active == 0;
    wr_key_during_hash        == 0;
    wr_config_during_hash     == 0;
  }

  //msg[] is a streaming msg input so can be of any size and needs its size dist-constrained
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

  constraint wipe_secret_c {
    do_wipe_secret == NoWipeSecret;
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [7:0] msg_q[$];
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, message size %0d bits, hmac=%0d, sha=%0d",
                i, num_trans, msg.size()*8, hmac_en, sha_en), UVM_LOW)
      `uvm_info(`gfn, $sformatf("digest size=%4b, key length=%6b",
                digest_size, key_length), UVM_LOW)
      `uvm_info(`gfn, $sformatf("intr_fifo_empty/hmac_done/hmac_err_en=%b, endian/digest_swap=%b",
                {intr_fifo_empty_en, intr_hmac_done_en, intr_hmac_err_en},
                {endian_swap, digest_swap}), UVM_LOW)
      `uvm_info(`gfn, $sformatf("wipe secret condition is: %0s", do_wipe_secret.name()), UVM_LOW)

      // initialize hmac configs
      hmac_init(.sha_en(sha_en), .hmac_en(hmac_en), .endian_swap(endian_swap),
                .digest_swap(digest_swap), .digest_size(digest_size), .key_length(key_length),
                .intr_fifo_empty_en(intr_fifo_empty_en),
                .intr_hmac_done_en(intr_hmac_done_en), .intr_hmac_err_en(intr_hmac_err_en));

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

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      if (do_wipe_secret == WipeSecretBeforeKey) begin
        `uvm_info(`gfn, $sformatf("wiping before key"), UVM_LOW)
        wipe_secrets();
        // Check if digest data are corrupted by wiping secrets.
        rd_digest();
      end

      // write key
      wr_key(key);

      // randomly read previous digest, if the previous digest is not corrupted by wipe_secret
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      if (do_wipe_secret == WipeSecretBeforeStart) begin
        `uvm_info(`gfn, $sformatf("wiping before start"), UVM_LOW)
        wipe_secrets();
        // Here the wipe secret will only corrupt secret keys and current digests.
        // If HMAC is not enabled, check if digest is corrupted.
        if (!hmac_en) rd_digest();
      end

      if (sha_en || $urandom_range(0, 1)) begin
        bit [TL_DW-1:0] intr_state_val;
        // start stream in msg
        fork
          begin
            if (do_hash_start) trigger_hash();
            if (invalid_cfg & do_hash_start) begin // error would only be signalled when started
              // wait for interrupt to assert, check status and clear it
              if (intr_hmac_err_en) begin
                `DV_WAIT(cfg.intr_vif.pins[HmacErr] === 1'b1);
              end else begin
                csr_spinwait(.ptr(ral.intr_state.hmac_err), .exp_data(1'b1));
              end
              `uvm_info(`gfn, $sformatf("HMAC Error,  %b", cfg.intr_vif.pins[HmacErr]), UVM_LOW)
            end
            if (do_burst_wr) burst_wr_msg(msg, burst_wr_length);
            else             wr_msg(msg);
          end
          begin
            if (do_wipe_secret == WipeSecretBeforeProcess) begin
              `uvm_info(`gfn, $sformatf("wiping before process"), UVM_LOW)
              cfg.clk_rst_vif.wait_clks($urandom_range(0, msg.size() * 10));
              wipe_secrets();
            end
          end
        join

        if (!sha_en) begin
          if (re_enable_sha) begin // restream in the message
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
          fork
            begin
              if (!invalid_cfg) begin
                // wait for interrupt to assert, check status and clear it
                if (intr_hmac_done_en) begin
                  `DV_WAIT(cfg.intr_vif.pins[HmacDone] === 1'b1);
                end else begin
                  csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
                end
              end
            end
            begin
              if (do_wipe_secret == WipeSecretBeforeDone) begin
                        `uvm_info(`gfn, $sformatf("wiping before done"), UVM_LOW)

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
      if ($urandom_range(0, 1)) rd_msg_length();

      // read digest from DUT
      `uvm_info(`gfn, $sformatf("reading digest now"), UVM_HIGH)
      rd_digest();
    end
    // Ensure that wipe secret flag is cleared for the next sequence, as it may cause digest
    // comparison issue with the stress tests
    clear_wipe_secret();
  endtask : body

endclass : hmac_smoke_vseq
