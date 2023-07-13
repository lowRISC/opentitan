// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the `ispr_rdata_intg_i` signal of
// `otbn_controller` while OTBN is still running.

class otbn_controller_ispr_rdata_err_vseq extends otbn_intg_err_vseq;
  `uvm_object_utils(otbn_controller_ispr_rdata_err_vseq)

  `uvm_object_new

  protected task await_use(output bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words);
    used_words = '0;
    `uvm_info(`gfn, "Waiting for `ispr_rdata_intg` to be used", UVM_LOW)
    cfg.controller_vif.wait_for_ispr_rdata_used(200, used_words);
  endtask

  protected task inject_errors(input  bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words,
                               output bit [otbn_pkg::BaseWordsPerWLEN-1:0] corrupted_words);
    int unsigned corrupt_word_pct[otbn_pkg::BaseWordsPerWLEN];
    bit [otbn_pkg::ExtWLEN-1:0] new_data;

    for (int i_word = 0; i_word < otbn_pkg::BaseWordsPerWLEN; i_word++) begin
      if (used_words[i_word]) begin
        // Corrupt used words with a fairly high chance.
        corrupt_word_pct[i_word] = 75;
      end else begin
        // Corrupt unused words with a lower chance.
        corrupt_word_pct[i_word] = 10;
      end
    end

    new_data = corrupt_data(cfg.controller_vif.ispr_rdata_intg_i,
                            corrupt_word_pct,
                            corrupted_words);

    if (corrupted_words != '0) begin
      `uvm_info(`gfn, "Injecting errors into `ispr_rdata_intg_i` of `otbn_controller`", UVM_LOW)
      cfg.controller_vif.force_ispr_rdata_intg_i(new_data);
    end else begin
      `uvm_info(`gfn, "Randomization decided to not inject any errors.", UVM_LOW)
    end
  endtask

  protected task release_force();
    cfg.controller_vif.release_ispr_rdata_intg_i();
  endtask

endclass
