// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_stress_all_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_stress_all_vseq)
  `uvm_object_new

  task body();
    string seq_names[] =  {
                           "rv_dm_smoke_vseq",
                           "rv_dm_tap_fsm_vseq",
                           "rv_dm_sba_tl_access_vseq",
                           "rv_dm_delayed_resp_sba_tl_access_vseq",
                           "rv_dm_bad_sba_tl_access_vseq"
                           };

    for (int i = 0; i < num_trans; i++) begin
      uvm_sequence seq;
      rv_dm_base_vseq rv_dm_vseq;
      uint seq_idx = $urandom_range(0, seq_names.size - 1);
      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(rv_dm_vseq, seq)

      rv_dm_vseq.do_apply_reset = 1;
      rv_dm_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(rv_dm_vseq)
      `uvm_info(`gfn, $sformatf("seq_idx = %0d, sequence is %0s", seq_idx,
                                rv_dm_vseq.get_name()), UVM_MEDIUM)
      rv_dm_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf("End of sequence %s with seq_idx = %0d",
                                rv_dm_vseq.get_name(), seq_idx), UVM_MEDIUM)
    end
  endtask // body
endclass
