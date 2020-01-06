// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test all hosts use same source id for each iteration
// reduce to 1-10 trans per iteration and increase interation number by x10
class xbar_same_source_vseq extends xbar_random_vseq;

  `uvm_object_utils(xbar_same_source_vseq)
  `uvm_object_new

  // reduce to 1-10 trans per iteration
  function void seq_init();
    min_req_cnt = 1;
    max_req_cnt = 10;
    super.seq_init();
  endfunction

  virtual function void update_host_seq();
    int source = $urandom_range(0, (1 << cfg.valid_host_id_width) - 1);

    if (cfg.en_cov) cov.same_source_access_cg.sample(source);
    `uvm_info(`gfn, $sformatf("Picked source (%0d) for all hosts", source), UVM_HIGH)

    // change host to only access the picked device
    foreach (host_seq[i]) begin
      host_seq[i].override_a_source_val = 1;
      host_seq[i].overridden_a_source_val = source;
    end
  endfunction

endclass
