// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_common_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  bit first_reset;

  virtual task pre_start();
    string common_seq_type;
    void'($value$plusargs("run_%0s", common_seq_type));

    // To avoid reading out unknown data from mem, do init for mem test after 1st reset
    if (!uvm_re_match("*mem*", common_seq_type) && !first_reset) begin
      do_sram_ctrl_init = 1;
      first_reset       = 1;
    end else begin
      do_sram_ctrl_init = 0;
    end

    super.pre_start();

    // After init, init_done is set. If scb is off, update predict value here
    if (!cfg.en_scb && do_sram_ctrl_init) begin
      void'(ral.status.init_done.predict(.value(1), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
