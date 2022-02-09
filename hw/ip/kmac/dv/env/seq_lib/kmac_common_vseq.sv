// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_common_vseq extends kmac_base_vseq;
  `uvm_object_utils(kmac_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    do_kmac_init = 1'b0;
    entropy_mode_c.constraint_mode(0);
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void predict_shadow_reg_status(bit predict_update_err  = 0,
                                                  bit predict_storage_err = 0);
    super.predict_shadow_reg_status(predict_update_err, predict_storage_err);

    if (predict_storage_err) begin
      // For storage error, the kmac `cfg_regwen` register will be set to 0 internally to lock all
      // cfg related CSRs. Because it is a `RO` register, the logic below manually locks the write
      // access for its lockable register fields. (If the regwen is `W0C` access policy, the
      // lockable fields will be updated automatically in `do_predict` function)
      ral.cfg_regwen.en.set_lockable_flds_access(.lock(1));

      // TODO(Issue #8460) - shadow storage error will clear update error status bit.
      foreach (cfg.shadow_update_err_status_fields[status_field]) begin
        void'(status_field.predict(~cfg.shadow_update_err_status_fields[status_field]));
      end
    end
  endfunction
endclass
