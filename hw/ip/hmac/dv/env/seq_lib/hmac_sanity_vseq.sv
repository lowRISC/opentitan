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
  rand bit        endian_swap;
  rand bit        digest_swap;
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

  constraint burst_wr_c {
    burst_wr_length inside {[1 : HMAC_MSG_FIFO_DEPTH]};
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [7:0] msg_q[$];
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, message size %0d, hmac=%0d",
                                i, num_trans, msg.size(), hmac_en), UVM_LOW)
      // hmac_init only sha
      hmac_init(.hmac_en(hmac_en), .endian_swap(endian_swap), .digest_swap(digest_swap));

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      // write key
      wr_key(key);

      // can randomly read previous digest
      if (i != 1 && $urandom_range(0, 1)) rd_digest();

      // start stream in msg
      trigger_hash();

      if (do_burst_wr) burst_wr_msg(msg, burst_wr_length);
      else wr_msg(msg);

      // msg stream in finished, start hash
      trigger_process();

      // wait for interrupt to assert, check status and clear it
      wait(cfg.intr_vif.pins[HmacDone] === 1'b1);
      check_interrupts(.interrupts((1 << HmacDone)), .check_set(1'b1));

      // read msg fifo length
      rd_msg_length();

      // read digest from DUT
      rd_digest();
    end
  endtask : body

endclass : hmac_sanity_vseq
