// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will randomly issue key otbn, sram, flash key requests during or after partition
// is locked.
// This sequence will check if nonce, seed_valid, and output keys are correct via scb.

class otp_ctrl_rand_key_rsp_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_rand_key_rsp_vseq)

  `uvm_object_new

  constraint num_iterations_c {
    num_trans  inside {[1:5]};
    num_dai_op inside {[1:500]};
  }

  function void pre_randomize();
    this.dai_wr_blank_addr_c.constraint_mode(0);
    collect_used_addr = 0;
  endfunction

  virtual task body();
    bit base_vseq_done;

    fork
      begin
        key_requests(base_vseq_done);
      end
      begin
        super.body();
        base_vseq_done = 1;
      end
    join
  endtask

  virtual task key_requests(ref bit base_vseq_done);
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

  virtual task wait_clk_or_reset(int wait_clks);
    repeat(wait_clks) begin
      @(posedge cfg.clk_rst_vif.clk);
      if (cfg.under_reset) break;
    end
  endtask

endclass
