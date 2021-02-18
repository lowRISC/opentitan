// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will randomly issue key otbn, sram, flash key requests during or after partition
// is locked.
// This sequence will check if nonce, seed_valid, and output keys are correct via scb.

class otp_ctrl_parallel_key_req_vseq extends otp_ctrl_parallel_base_vseq;
  `uvm_object_utils(otp_ctrl_parallel_key_req_vseq)

  `uvm_object_new

  constraint key_reqs_c {
    do_req_keys == 0;
  }

  virtual task run_parallel_seq(ref bit base_vseq_done);
    forever
      begin
        if (base_vseq_done) return;

        fork
          begin
            // get otbn keys
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_otbn_key();
            end
          end
          begin
            // get flash addr key
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_flash_addr_key();
            end
          end
          begin
            // get flash datta key
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_flash_data_key();
            end
          end
          begin
            // get sram keys
            if ($urandom_range(0, 1)) begin
              wait_clk_or_reset($urandom_range(0, 500));
              if (!base_vseq_done && !cfg.under_reset) req_all_sram_keys();
            end
          end
        join
      end
  endtask

endclass
