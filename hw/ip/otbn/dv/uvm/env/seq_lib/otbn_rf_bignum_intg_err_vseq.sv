// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to insert 1 or 2 bit flips per word to bignum register file while
// OTBN is trying to read from it.

class otbn_rf_bignum_intg_err_vseq extends otbn_intg_err_vseq;
  `uvm_object_utils(otbn_rf_bignum_intg_err_vseq)

  `uvm_object_new
  rand bit insert_intg_err_to_a;

  protected task await_use(output bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words);
    logic rd_en;
    used_words = '0;
    `uvm_info(`gfn, "Waiting for selected RF to be used", UVM_LOW)
    `DV_SPINWAIT_EXIT(
      do begin
        @(cfg.clk_rst_vif.cbn);
        rd_en = insert_intg_err_to_a ? cfg.trace_vif.rf_bignum_rd_en_a :
                                       cfg.trace_vif.rf_bignum_rd_en_b;
      end while(!rd_en); used_words = '1;,
      cfg.clk_rst_vif.wait_clks(2000);,
      "Not getting selected rd_en from OTBN for 2000 cycles!"
    )
  endtask

  protected task inject_errors(input  bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words,
                               output bit [otbn_pkg::BaseWordsPerWLEN-1:0] corrupted_words);
    logic [otbn_pkg::ExtWLEN-1:0] orig_data;
    bit   [otbn_pkg::ExtWLEN-1:0] new_data;

    orig_data = insert_intg_err_to_a ? cfg.trace_vif.rf_bignum_rd_data_a_intg :
                                       cfg.trace_vif.rf_bignum_rd_data_b_intg;
    new_data = corrupt_data(orig_data, '{default: 100}, corrupted_words);

    if (corrupted_words != '0) begin
      `uvm_info(`gfn, "Injecting errors into Bignum RF", UVM_LOW)
      if (insert_intg_err_to_a) begin
        cfg.trace_vif.force_rf_bignum_rd_data_a_intg(new_data);
      end else begin
        cfg.trace_vif.force_rf_bignum_rd_data_b_intg(new_data);
      end
    end else begin
      `uvm_info(`gfn, "Randomization decided to not inject any errors.", UVM_LOW)
    end
  endtask

  protected task release_force();
    if (insert_intg_err_to_a) begin
      cfg.trace_vif.release_rf_bignum_rd_data_a_intg();
    end else begin
      cfg.trace_vif.release_rf_bignum_rd_data_b_intg();
    end
  endtask

endclass
