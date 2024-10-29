// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sequence to stress test with reset and extended runtime
class pwm_stress_all_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_stress_all_vseq)
  `uvm_object_new

  // Constrain things so we run five sequences each time. This should be enough to "run some
  // back-to-back", but avoids needing to run lots sequentially (so avoids a large runtime)
  constraint num_trans_c { num_trans == 5; }

  constraint duration_cycles_c {
    duration_cycles dist {
      (NUM_CYCLES):/8,
      (2 * NUM_CYCLES):/4,
      (4 * NUM_CYCLES):/2,
      (8 * NUM_CYCLES):/1
      };
  }


  virtual task body();
    string seq_names[] = {"pwm_smoke_vseq",
                          "pwm_common_vseq",
                          "pwm_perf_vseq",
                          "pwm_rand_output_vseq"};

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      pwm_base_vseq  pwm_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);
      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(pwm_vseq, seq)

      pwm_vseq.do_apply_reset = 0;
      pwm_vseq.set_sequencer(p_sequencer);
      `uvm_info(`gfn, $sformatf("Running %s sequence", seq_names[seq_idx]), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(pwm_vseq)
      if (seq_names[seq_idx] == "pwm_common_vseq") begin
        pwm_common_vseq common_vseq;
        `downcast(common_vseq, pwm_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      pwm_vseq.start(p_sequencer);
    end
  endtask : body

endclass : pwm_stress_all_vseq
