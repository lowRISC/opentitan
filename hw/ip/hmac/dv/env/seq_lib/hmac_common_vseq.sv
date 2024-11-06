// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_common_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_common_vseq)

  rand bit trig_rst_during_hash;

  // Constraints
  extern constraint trig_rst_during_hash_c;
  extern constraint num_trans_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task pre_start();
  extern task body();

  // Class specific methods
  extern task wait_to_issue_reset(uint reset_delay_bound);
endclass : hmac_common_vseq


constraint hmac_common_vseq::trig_rst_during_hash_c {
  trig_rst_during_hash dist {
    1 :/ 1,
    0 :/ 9
  };
}

constraint hmac_common_vseq::num_trans_c {
  num_trans inside {[1:3]};
}

function hmac_common_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_common_vseq::pre_start();
  do_hmac_init = 1'b0;
  super.pre_start();
endtask : pre_start

task hmac_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask : body

task hmac_common_vseq::wait_to_issue_reset(uint reset_delay_bound);
  `DV_CHECK_MEMBER_RANDOMIZE_FATAL(trig_rst_during_hash)

  if (trig_rst_during_hash) begin
    // In hmac_core, the FSM `StPushToMsgFifo` only spans around 20 clock cycles in the entire
    // hashing process. So to ensure hmac won't corrupt if reset is issued during
    // `StPushToMsgFifo` state, this task try to issue reset (with a large possibility) during
    // `StPushToMsgFifo` state.
    wait (cfg.hash_process_triggered == 1);
    super.wait_to_issue_reset($urandom_range(100, 150));
    #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
  end else begin
    super.wait_to_issue_reset(reset_delay_bound);
  end
  cfg.hash_process_triggered = 0;
endtask : wait_to_issue_reset
