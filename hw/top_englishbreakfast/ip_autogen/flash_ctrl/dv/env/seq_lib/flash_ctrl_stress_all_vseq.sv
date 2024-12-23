// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_stress_all_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_stress_all_vseq)
  `uvm_object_new

  task body();
    string seq_names[] = {
      "flash_ctrl_smoke_vseq",
      "flash_ctrl_smoke_hw_vseq"
                          };

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence     seq;
      flash_ctrl_base_vseq flash_ctrl_vseq;
      uint             seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(flash_ctrl_vseq, seq)

      flash_ctrl_vseq.do_apply_reset = 1;
      flash_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(flash_ctrl_vseq)
      `uvm_info(`gfn, $sformatf("seq_idx = %0d, sequence is %0s", seq_idx,
                                flash_ctrl_vseq.get_name()), UVM_MEDIUM)

      flash_ctrl_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf(
                "End of sequence %0s with seq_idx = %0d",
                flash_ctrl_vseq.get_name(), seq_idx), UVM_MEDIUM)
    end
  endtask // body

endclass // flash_ctrl_stress_all_vseq
