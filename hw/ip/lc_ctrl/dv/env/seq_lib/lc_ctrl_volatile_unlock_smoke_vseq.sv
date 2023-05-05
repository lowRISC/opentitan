// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// set volatile unlock to 1 and check if raw -> unlock0 transition is successful.
class lc_ctrl_volatile_unlock_smoke_vseq extends lc_ctrl_jtag_access_vseq;

  rand dec_lc_state_e next_state;
  rand bit next_state_is_testunlock0;

  `uvm_object_utils(lc_ctrl_volatile_unlock_smoke_vseq)
  `uvm_object_new

  constraint next_state_c {
      if (next_state_is_testunlock0) next_state == DecLcStTestUnlocked0;
      solve next_state_is_testunlock0 before next_state;
   }

  task body();
    `DV_CHECK_RANDOMIZE_FATAL(this)
    // TODO: randomize that not always start with raw state.
    drive_otp_i(0);
    if (lc_cnt != LcCnt24) begin
      lc_ctrl_state_pkg::lc_token_t token_val = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
      csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
      csr_wr(ral.transition_ctrl.volatile_raw_unlock, 1);
      csr_wr(ral.transition_target, {DecLcStateNumRep{next_state[DecLcStateWidth-1:0]}});
      foreach (ral.transition_token[i]) begin
        csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
        token_val = token_val >> TL_DW;
      end
      csr_wr(ral.transition_cmd, 'h01);

      if (next_state == DecLcStTestUnlocked0) begin
        `DV_SPINWAIT(while (1) begin
            bit [TL_DW-1:0] status_val;
            csr_rd(ral.status, status_val);
            if (get_field_val(ral.status.transition_successful, status_val)) break;
          end)
          // TODO: check can keep programming next state.
      end else begin
        `DV_SPINWAIT(while (1) begin
            bit [TL_DW-1:0] status_val;
            csr_rd(ral.status, status_val);
            if (get_field_val(ral.status.transition_error, status_val)) break;
          end)
      end
    end

  endtask : body

endclass : lc_ctrl_volatile_unlock_smoke_vseq
