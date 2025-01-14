// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all rom seqs in one seq to run sequentially
class rom_ctrl_stress_all_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_stress_all_vseq)

  `uvm_object_new

  // If the upper sequence has disabled do_apply_reset for this sequence (probably because it's
  // stress_all_with_rand_reset), we aren't going to be able to allow the child sequences we start
  // to apply a reset either.
  //
  // But rom_ctrl is a bit unusual: the only way of testing it is to come out of a reset! So
  // constrain num_trans to be 1 in this situation: we are presumably coming out of a reset now but
  // won't be able to inject any more.
  //
  // If the upper sequence allows us to apply reset, we can run several transactions. Pick 3,
  // allowing several sequences back-to-back.
  extern constraint num_trans_c;

  extern task body();
endclass

constraint rom_ctrl_stress_all_vseq::num_trans_c {
  if (!do_apply_reset) {
    num_trans == 1;
  } else {
    num_trans == 3;
  }
}

task rom_ctrl_stress_all_vseq::body();
  string seq_names[] = {"rom_ctrl_smoke_vseq", "rom_ctrl_kmac_err_chk_vseq"};
  for (int i = 1; i <= num_trans; i++) begin
    uvm_sequence   seq;
    rom_ctrl_base_vseq rom_ctrl_vseq;
    uint           seq_idx = $urandom_range(0, seq_names.size - 1);
    seq = create_seq_by_name(seq_names[seq_idx]);
    `downcast(rom_ctrl_vseq, seq)

    // Tell the child sequence to start with a reset (because a rom_ctrl vseq only really makes
    // sense after a reset) unless this is the first iteration, in which case we can use the reset
    // that we just saw.
    rom_ctrl_vseq.do_apply_reset = (i > 1);

    rom_ctrl_vseq.set_sequencer(p_sequencer);
    `uvm_info(`gfn, $sformatf("Running %s sequence", seq_names[seq_idx]), UVM_LOW)
    `DV_CHECK_RANDOMIZE_FATAL(rom_ctrl_vseq)

    rom_ctrl_vseq.start(p_sequencer);

    // We've just got to the end of a sequence. Since we don't do anything after this loop, copy the
    // sequence's expected alert status to *this* sequence so that the post_start task expects the
    // same thing as the sequence we just ran.
    expect_fatal_alerts = rom_ctrl_vseq.expect_fatal_alerts;
  end
endtask : body
