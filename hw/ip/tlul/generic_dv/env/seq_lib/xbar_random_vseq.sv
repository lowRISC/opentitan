// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// base random seq, most of xbar vseq will extend from this
class xbar_random_vseq extends xbar_base_vseq;

  `uvm_object_utils(xbar_random_vseq)
  `uvm_object_new

  // override it to control host seq in extended classes
  virtual function void update_host_seq();
  endfunction

  virtual task body();
    run_all_device_seq_nonblocking();
    for (int i = 1; i <= num_trans; i++) begin
      update_host_seq();
      run_all_host_seq_in_parallel();
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
      // re-randomize for next loop
      if (i <= num_trans) `DV_CHECK_RANDOMIZE_FATAL(this)
    end
  endtask

endclass
