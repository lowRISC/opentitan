// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_base_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_target_base_seq)
  `uvm_object_new

  virtual task body();
    // i2c_item needs more test specific parameters for proper randomization.
    // Rather than keeping duplicate parameters in i2c_agent_cfg and i2c_seq_cfg,
    // use i2c_seq_cfg parameters to simplify implementation.
    // So, instead of randomizing i2c_item here, assuming i2c_item is randomized in
    // vseq and fed to req_q here.
    `DV_SPINWAIT_EXIT(wait (req_q.size() > 0);
                      while (req_q.size() > 0) begin
                        req = req_q.pop_front();
                        start_item(req);
                        finish_item(req);
                      end
                      , wait (stop);)
  endtask : body

endclass : i2c_target_base_seq
