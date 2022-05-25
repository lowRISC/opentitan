// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the `ispr_rdata_intg_i` signal of
// `otbn_controller` while OTBN is still running.

class otbn_controller_ispr_rdata_err_vseq extends otbn_intg_err_vseq;
  `uvm_object_utils(otbn_controller_ispr_rdata_err_vseq)

  `uvm_object_new

  task await_use(output bit used);
    used = 1'b0;
    `uvm_info(`gfn, "Waiting for `ispr_rdata_intg` to be used", UVM_LOW)
    cfg.controller_vif.wait_for_ispr_rdata_used(200, used);
  endtask

  task inject_errors(output bit corrupted);
    bit [otbn_pkg::ExtWLEN-1:0] new_data = corrupt_data(cfg.controller_vif.ispr_rdata_intg_i, 50,
                                                        corrupted);
    if (corrupted) begin
      `uvm_info(`gfn, "Injecting errors into `ispr_rdata_intg_i` of `otbn_controller`", UVM_LOW)
      cfg.controller_vif.force_ispr_rdata_intg_i(new_data);
    end else begin
      `uvm_info(`gfn, "Randomization decided to not inject any errors.", UVM_LOW)
    end
  endtask

  task release_force();
    cfg.controller_vif.release_ispr_rdata_intg_i();
  endtask

endclass
