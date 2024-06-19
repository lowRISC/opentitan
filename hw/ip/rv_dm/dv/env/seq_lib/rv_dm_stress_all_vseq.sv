// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_stress_all_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[5:9]};
  }

  task body();
    string seq_names[] = {
                          "rv_dm_mem_tl_access_resuming_vseq",
                          "rv_dm_halt_resume_whereto_vseq",
                          "rv_dm_cmderr_busy_vseq",
                          "rv_dm_smoke_vseq",
                          "rv_dm_ndmreset_req_vseq",
                          "rv_dm_mem_tl_access_halted_vseq",
                          "rv_dm_cmderr_not_supported_vseq",
                          "rv_dm_hart_unavail_vseq",
                          "rv_dm_jtag_dtm_hard_reset_vseq",
                          "rv_dm_jtag_dmi_dm_inactive_vseq",
                          "rv_dm_jtag_dtm_idle_hint_vseq",
                          "rv_dm_jtag_dmi_debug_disabled_vseq"
                          };
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence    seq;
      rv_dm_base_vseq rv_dm_vseq;
      uint            seq_idx = $urandom_range(0, seq_names.size - 1);

      `uvm_info(`gfn,
                $sformatf("Starting sequence %0s (trans %0d / %0d)",
                          seq_names[seq_idx], i, num_trans),
                UVM_LOW)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(rv_dm_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset.
      if (do_apply_reset) rv_dm_vseq.do_apply_reset = $urandom_range(0, 1);
      else                rv_dm_vseq.do_apply_reset = 0;

      rv_dm_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(rv_dm_vseq)
      rv_dm_vseq.start(p_sequencer);
     end
   endtask

endclass : rv_dm_stress_all_vseq
