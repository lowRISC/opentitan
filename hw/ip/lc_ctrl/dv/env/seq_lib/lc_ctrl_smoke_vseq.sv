// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class lc_ctrl_smoke_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_smoke_vseq)

  `uvm_object_new

  rand dec_lc_state_e next_lc_state;

  constraint lc_cnt_c {
    lc_state != LcStRaw -> lc_cnt != LcCntRaw;
  }

  constraint valid_next_lc_state_c {
    // TODO: temp constraint, did not enable ram interface
    next_lc_state != DecLcStRma;
    lc_state == LcStRma     -> next_lc_state inside {DecLcStScrap};
    lc_state == LcStProdEnd -> next_lc_state inside {DecLcStScrap};
    lc_state == LcStProd    -> next_lc_state inside {DecLcStScrap, DecLcStRma};
    lc_state == LcStDev     -> next_lc_state inside {DecLcStScrap, DecLcStRma};

    lc_state == LcStTestUnlocked3 -> next_lc_state inside
                {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev};

    lc_state == LcStTestLocked2   -> next_lc_state inside
                {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev, DecLcStTestUnlocked3};

    lc_state == LcStTestUnlocked2 -> next_lc_state inside
                {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev, DecLcStTestLocked2};

    lc_state == LcStTestLocked1   -> next_lc_state inside
                {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev, DecLcStTestUnlocked3,
                 DecLcStTestUnlocked2};

    lc_state == LcStTestUnlocked1 -> next_lc_state inside
                {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                 DecLcStTestLocked2, DecLcStTestLocked1};

    lc_state == LcStTestLocked0   -> next_lc_state inside
                {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev, DecLcStTestUnlocked3,
                 DecLcStTestUnlocked2, DecLcStTestUnlocked1};

    lc_state == LcStTestUnlocked0 -> next_lc_state inside
                {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                 DecLcStTestLocked2, DecLcStTestLocked1, DecLcStTestLocked0};

    lc_state == LcStRaw -> next_lc_state inside
                {DecLcStScrap, DecLcStTestUnlocked2, DecLcStTestUnlocked1, DecLcStTestUnlocked0};
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      if (i != 1) dut_init();

      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                                i, num_trans, lc_state.name, lc_cnt.name), UVM_MEDIUM)

      // SW transition request
      if (lc_state != LcStScrap && lc_cnt != LcCnt16) begin
        bit [TL_DW-1:0] token_val = $urandom();
        sw_transition_req(next_lc_state, token_val);
      end
    end
  endtask : body

endclass : lc_ctrl_smoke_vseq
