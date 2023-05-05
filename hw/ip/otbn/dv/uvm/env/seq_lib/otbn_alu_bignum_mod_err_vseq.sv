// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the `mod_intg_q` register of
// `otbn_alu_bignum` while OTBN is still running.

class otbn_alu_bignum_mod_err_vseq extends otbn_intg_err_vseq;
  `uvm_object_utils(otbn_alu_bignum_mod_err_vseq)

  `uvm_object_new

  protected task await_use(output bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words);
    used_words = '0;
    `uvm_info(`gfn, "Waiting for `mod_intg_q` to be used", UVM_LOW)
    cfg.alu_bignum_vif.wait_for_mod_used(200, used_words);
  endtask

  protected task inject_errors(input  bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words,
                               output bit [otbn_pkg::BaseWordsPerWLEN-1:0] corrupted_words);
    bit [otbn_pkg::ExtWLEN-1:0] new_data = corrupt_data(cfg.alu_bignum_vif.mod_intg_q,
                                                        '{default: 50},
                                                        corrupted_words);
    if (corrupted_words != '0) begin
      `uvm_info(`gfn, "Injecting errors into `mod_intg_q` of `otbn_alu_bignum`", UVM_LOW)
      cfg.alu_bignum_vif.force_mod_intg_q(new_data);
    end else begin
      `uvm_info(`gfn, "Randomization decided to not inject any errors.", UVM_LOW)
    end
  endtask

  protected task release_force();
    cfg.alu_bignum_vif.release_mod_intg_q();
  endtask

endclass
