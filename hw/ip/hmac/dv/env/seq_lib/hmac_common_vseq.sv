// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_common_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_common_vseq)
  `uvm_object_new

  rand bit trigger_reset_during_hash_process;

  constraint trigger_reset_during_hash_process_c {
    trigger_reset_during_hash_process dist {
      1 :/ 1,
      0 :/ 9
    };
  }

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task pre_start();
    do_hmac_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task wait_to_issue_reset(uint reset_delay_bound = 10_000_000);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(trigger_reset_during_hash_process)

    if (trigger_reset_during_hash_process) begin
      // In hmac_core, the FSM `StPushToMsgFifo` only spans around 20 clock cycles in the entire
      // hashing process. So to ensure hmac won't corrupt if reset is issued during
      // `StPushToMsgFifo` state, this task try to issue reset (with a large possibility) during
      // `StPushToMsgFifo` state.
      wait (cfg.hash_process_triggered == 1);
      cfg.clk_rst_vif.wait_clks($urandom_range(100, 150));
      #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
    end else begin
      super.wait_to_issue_reset(reset_delay_bound);
    end
    cfg.hash_process_triggered = 0;
  endtask : wait_to_issue_reset

endclass
