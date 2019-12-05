// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_sanity_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_sanity_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:100]};
  }

  rand bit        hmac_en;
  rand bit        sha_en;
  rand bit        endian_swap;
  rand bit        digest_swap;
  rand bit        intr_fifo_full_en;
  rand bit        intr_hmac_done_en;
  rand bit        intr_hmac_err_en;
  rand bit [31:0] key[8];
  rand bit [7:0]  msg[];
  rand int        burst_wr_length;

  constraint msg_c {
    msg.size() dist {
        0       :/ 1,
        [1 :60] :/ 8,
        [61:64] :/ 1
    }; // upto 64 bytes (16 words, 512 bits)
  }

  constraint sha_en_c {
    sha_en dist {1'b1 := 9, 1'b0 := 1};
  }

  constraint burst_wr_c {
    burst_wr_length inside {[1 : HMAC_MSG_FIFO_DEPTH]};
  }

  constraint intr_enable_c {
    intr_fifo_full_en dist {1'b1 := 8, 1'b0 := 2};
    intr_hmac_done_en dist {1'b1 := 8, 1'b0 := 2};
    intr_hmac_err_en  dist {1'b1 := 8, 1'b0 := 2};
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    run_alert_rsp_seq_nonblocking();
    for (int i = 1; i <= num_trans; i++) begin
      bit [7:0] msg_q[$];
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, message size %0d, hmac=%0d, sha=%0d",
                                i, num_trans, msg.size(), hmac_en, sha_en), UVM_LOW)
      `uvm_info(`gfn, $sformatf("intr_fifo_full/hmac_done/hmac_err_en=%b, endian/digest_swap=%b",
                                {intr_fifo_full_en, intr_hmac_done_en, intr_hmac_err_en},
                                {endian_swap, digest_swap}), UVM_HIGH)
      // initialize hmac configs
      hmac_init(.sha_en(sha_en), .hmac_en(hmac_en), .endian_swap(endian_swap),
                .digest_swap(digest_swap), .intr_fifo_full_en(intr_fifo_full_en),
                .intr_hmac_done_en(intr_hmac_done_en), .intr_hmac_err_en(intr_hmac_err_en));

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      // write key
      wr_key(key);

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      if (sha_en || $urandom_range(0, 1)) begin
        // start stream in msg
        trigger_hash();

        if (do_burst_wr) burst_wr_msg(msg, burst_wr_length);
        else wr_msg(msg);
        if (!sha_en) begin
          if ($urandom_range(0, 1)) begin // restream in the message
            sha_enable();
            trigger_hash();
            wr_msg(msg);
          end else begin // discard current transaction
            continue;
          end
        end
        // msg stream in finished, start hash
        trigger_process();

        // fifo_full intr can be triggered at the latest two cycle after process
        // example: current fifo_depth=(14 words + 2 bytes), then wr last 4 bytes, design will
        // process the 15th word then trigger intr_fifo_full
        cfg.clk_rst_vif.wait_clks(2);
        clear_intr_fifo_full();

        // wait for interrupt to assert, check status and clear it
        if (intr_hmac_done_en) begin
          wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
          check_interrupts(.interrupts((1 << HmacDone)), .check_set(1'b1));
        end else begin
          csr_spinwait(.ptr(ral.intr_state.hmac_done), .exp_data(1'b1));
          csr_wr(.csr(ral.intr_state), .value(1 << HmacDone));
        end
      end

      // if disable sha, digest should be cleared
      // read msg fifo length
      rd_msg_length();

      // read digest from DUT
      rd_digest();
    end
  endtask : body

endclass : hmac_sanity_vseq
