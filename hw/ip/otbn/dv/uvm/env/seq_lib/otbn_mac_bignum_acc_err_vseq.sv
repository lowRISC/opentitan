// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the `acc_intg_q` register of
// `otbn_mac_bignum` while OTBN is still running.

class otbn_mac_bignum_acc_err_vseq extends otbn_intg_err_vseq;
  `uvm_object_utils(otbn_mac_bignum_acc_err_vseq)

  `uvm_object_new

  task await_use(output bit used);
    used = 1'b0;
    `uvm_info(`gfn, "Waiting for `acc_intg_q` to be used", UVM_LOW)
    cfg.mac_bignum_vif.wait_for_acc_used(200, used);
  endtask

  task inject_errors(output bit corrupted);
    bit [otbn_pkg::ExtWLEN-1:0] new_data = corrupt_data(cfg.mac_bignum_vif.acc_intg_q, 50,
                                                        corrupted);
    if (corrupted) begin
      `uvm_info(`gfn, "Injecting errors into `acc_intg_q` of `otbn_mac_bignum`", UVM_LOW)
      cfg.mac_bignum_vif.force_acc_intg_q(new_data);
    end else begin
      `uvm_info(`gfn, "Randomization decided to not inject any errors.", UVM_LOW)
    end
  endtask

  task release_force();
    cfg.mac_bignum_vif.release_acc_intg_q();
  endtask

endclass
