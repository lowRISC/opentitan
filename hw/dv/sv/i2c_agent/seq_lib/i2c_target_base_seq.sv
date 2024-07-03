// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_base_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_target_base_seq)
  `uvm_object_new

  virtual task body();
    // A sequence of i2c_items that are randomized in the vseq are fed into the req_q here.
    // This isn't ideal, and hopefully will be rethought in the future.
    // TODO(#14825) Randomize in the sequence, rather than the vseq. Or, compose a
    // transfer or transaction-level sequence item, randomize it, and then
    // decompose into individual driver op's in the agent sequnce (i.e. here).

    // Wait until we get stimulus from the vseq.
    wait (req_q.size() > 0);

    fork begin : iso_fork
      fork
        // Drive all items in the 'req_q'
        while (req_q.size() > 0) begin
          req = req_q.pop_front();
          start_item(req);
          finish_item(req);
        end
        // This process ends the stimulus generation if seq_stop() is called.
        // (Note. that any remaining driver stimulus in req_q is abandoned)
        wait(stop);
      join_any
      disable fork;
    end : iso_fork join
  endtask : body

endclass : i2c_target_base_seq
