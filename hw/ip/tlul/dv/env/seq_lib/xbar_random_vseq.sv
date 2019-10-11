// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment virtual sequence
// ---------------------------------------------
class xbar_random_vseq extends xbar_base_vseq;

  `uvm_object_utils(xbar_random_vseq)
  `uvm_object_new

  virtual task body();
    int completed_seq_cnt;

    run_device_seq_nonblocking();
    foreach (host_seq[i]) begin
      fork
        automatic int host_id = i;
        begin
          run_host_seq(host_id);
          completed_seq_cnt += 1;
        end
      join_none
    end
    wait (completed_seq_cnt == host_seq.size());
  endtask

endclass
