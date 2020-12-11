// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class lc_ctrl_smoke_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_smoke_vseq)

  `uvm_object_new

  dec_lc_state_e next_lc_state;

  constraint lc_cnt_c {
    lc_state != LcStRaw -> lc_cnt != LcCntRaw;
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      if (i != 1) dut_init();
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                                i, num_trans, lc_state.name, lc_cnt.name), UVM_MEDIUM)

      // SW transition request
      if (valid_state_for_trans(lc_state) && lc_cnt != LcCnt16) begin
        bit [TL_DW*3-1:0] token_val = {$urandom(), $urandom(), $urandom()};
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf("next_LC_state is %0s, input token is %0h", next_lc_state.name,
                                  token_val), UVM_DEBUG)
        sw_transition_req(next_lc_state, token_val);
      end
    end
  endtask : body

  // smoke test will always return valid next_lc_state
  // need to randomize here because associative array's index cannot be a rand input in constraint
  virtual function void randomize_next_lc_state(dec_lc_state_e curr_lc_state);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
        // TODO: temp constraint for no DecLcStRma
        next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]}; next_lc_state != DecLcStRma;)
  endfunction

endclass : lc_ctrl_smoke_vseq
