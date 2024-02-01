// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all rom seqs in one seq to run sequentially
class rom_ctrl_stress_all_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[3:6]};
  }

  task body();
    string seq_names[] = {"rom_ctrl_smoke_vseq",
                          "rom_ctrl_common_vseq"};
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      rom_ctrl_base_vseq rom_ctrl_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);
      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(rom_ctrl_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) rom_ctrl_vseq.do_apply_reset = $urandom_range(0, 1);
      else                rom_ctrl_vseq.do_apply_reset = 0;
      rom_ctrl_vseq.set_sequencer(p_sequencer);
      `uvm_info(`gfn, $sformatf("Running %s sequence", seq_names[seq_idx]), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(rom_ctrl_vseq)
      if (seq_names[seq_idx] == "rom_ctrl_common_vseq") begin
        rom_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, rom_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      rom_ctrl_vseq.start(p_sequencer);
    end
  endtask : body

endclass
