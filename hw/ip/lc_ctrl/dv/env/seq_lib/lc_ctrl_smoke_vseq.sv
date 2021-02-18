// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class lc_ctrl_smoke_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_smoke_vseq)

  `uvm_object_new

  rand bit clk_byp_error_rsp;
  rand bit flash_rma_error_rsp;
  rand bit trans_success;
  dec_lc_state_e next_lc_state;

  constraint no_err_rsps_c {
    clk_byp_error_rsp   == 0;
    flash_rma_error_rsp == 0;
  }

  constraint trans_success_c {
    trans_success == 1;
  }

  task body();
    run_clk_byp_rsp_nonblocking(clk_byp_error_rsp);
    run_flash_rma_rsp_nonblocking(flash_rma_error_rsp);

    for (int i = 1; i <= num_trans; i++) begin
      if (i != 1) dut_init();
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                                i, num_trans, lc_state.name, lc_cnt.name), UVM_MEDIUM)

      if ($urandom_range(0, 1)) begin
        csr_rd_check(.ptr(ral.status.ready), .compare_value(1));
        rd_lc_state_and_cnt_csrs();
      end

      // SW transition request
      if (valid_state_for_trans(lc_state) && lc_cnt != LcCnt16) begin
        bit [TL_DW*4-1:0] token_val = {$urandom(), $urandom(), $urandom(), $urandom()};
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf("next_LC_state is %0s, input token is %0h", next_lc_state.name,
                                  token_val), UVM_DEBUG)
        if (lc_state == LcStRaw && next_lc_state inside {DecLcStTestUnlocked0,
            DecLcStTestUnlocked1, DecLcStTestUnlocked2, DecLcStTestUnlocked3}) begin
          cfg.lc_ctrl_vif.set_hashed_token(lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed);
        end
        sw_transition_req(next_lc_state, token_val, trans_success);
      end else begin
        // wait at least two clks for scb to finish checking lc outputs
        cfg.clk_rst_vif.wait_clks($urandom_range(2, 10));
      end
    end
  endtask : body

  // smoke test will always return valid next_lc_state
  // need to randomize here because associative array's index cannot be a rand input in constraint
  virtual function void randomize_next_lc_state(dec_lc_state_e curr_lc_state);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
        next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]};)
  endfunction

endclass : lc_ctrl_smoke_vseq
