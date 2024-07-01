// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Write random value to claim_transition_if register, and check only
class lc_ctrl_claim_transition_if_vseq extends lc_ctrl_smoke_vseq;
  `uvm_object_utils(lc_ctrl_claim_transition_if_vseq)

  `uvm_object_new

  rand bit [TL_DW-1:0] rand_claim_trans_val;

  constraint rand_claim_trans_val_c {
    rand_claim_trans_val dist {
        CLAIM_TRANS_VAL :/ 1,
        [0 : CLAIM_TRANS_VAL-1] :/ 1,
        [CLAIM_TRANS_VAL+1 : $] :/ 1
    };
  }

  virtual task pre_start();
    super.pre_start();
    cfg.en_scb = 0;
  endtask

  task body();
    fork
      run_clk_byp_rsp(1'b0);
      run_flash_rma_rsp(1'b0);
    join_none

    csr_wr(ral.claim_transition_if, rand_claim_trans_val);
    `uvm_info(`gfn, $sformatf("write value %0h to claim_transition_if reg", rand_claim_trans_val),
              UVM_LOW)
    if ((rand_claim_trans_val & 'hff) == CLAIM_TRANS_VAL) begin
      csr_rd_check(.ptr(ral.claim_transition_if), .compare_value(CLAIM_TRANS_VAL));
      if (lc_state != LcStScrap) begin
        csr_rd_check(.ptr(ral.transition_regwen), .compare_value(1));
      end else begin
        csr_rd_check(.ptr(ral.transition_regwen), .compare_value(0));
      end
    end else begin
      csr_rd_check(.ptr(ral.claim_transition_if), .compare_value((rand_claim_trans_val & 'hff)));
      csr_rd_check(.ptr(ral.transition_regwen), .compare_value(0));
    end

  endtask : body

endclass : lc_ctrl_claim_transition_if_vseq
