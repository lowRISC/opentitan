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
  extern task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
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

// After a fatal fault, HMAC must lock up until the next reset: the digest registers read as zero
// and a newly started operation never completes.
task hmac_common_vseq::check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
  bit [TL_DW-1:0] digest[16];
  bit [TL_DW-1:0] intr_state;

  // Check that the fatal alert is triggered and keeps firing.
  super.check_sec_cm_fi_resp(if_proxy);

  // The digest registers must read as zero.
  csr_rd_digest(digest);
  foreach (digest[i]) begin
    `DV_CHECK_EQ(digest[i], '0, $sformatf("digest[%0d] not zero after fatal fault", i))
  end

  // Start a new operation on an empty message and check that it never completes.
  hmac_init();
  csr_wr(.ptr(ral.cmd), .value(1'b1 << HashStart));
  csr_wr(.ptr(ral.cmd), .value(1'b1 << HashProcess));
  // An HMAC/SHA-2 256 operation on an empty message completes in a few hundred cycles.
  cfg.clk_rst_vif.wait_clks(1000);
  csr_rd(.ptr(ral.intr_state), .value(intr_state));
  `DV_CHECK_EQ(intr_state[HmacDone], 1'b0, "hmac_done raised after fatal fault")
endtask : check_sec_cm_fi_resp
