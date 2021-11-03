// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_common_vseq extends lc_ctrl_base_vseq;

  `uvm_object_utils(lc_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    uvm_reg_data_t rdata=0;

    // Claim mutex
    csr_wr(ral.claim_transition_if, 'h5a);

    while(rdata != 'h5a) begin
      csr_rd(ral.claim_transition_if, rdata);
    end

    run_common_vseq_wrapper(num_trans);

  endtask : body

endclass
