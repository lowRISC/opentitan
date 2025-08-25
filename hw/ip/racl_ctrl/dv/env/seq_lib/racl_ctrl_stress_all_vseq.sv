// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs sequences one after the other.

class racl_ctrl_stress_all_vseq extends racl_ctrl_base_vseq;
  `uvm_object_utils(racl_ctrl_stress_all_vseq)

  // The sequences that we'll run back-to-back
  //
  // TODO: At the moment, there is only actually one sequence defined (racl_ctrl_smoke), which makes
  //       this a little silly. We're still defining racl_ctrl_stress_all_vseq already, because it
  //       means we can run tests like racl_ctrl_stress_all_with_rand_reset.
  local string vseq_names[$] = {
    "racl_ctrl_smoke_vseq"
  };

  extern function new (string name="");
  extern task body();

  // Create and run a child vseq with the given name
  extern local task run_child(string child_vseq_name);
endclass

function racl_ctrl_stress_all_vseq::new (string name="");
  super.new(name);
endfunction

task racl_ctrl_stress_all_vseq::body();
  fork
    super.body();
    begin
      `uvm_info(`gfn, $sformatf("Running %0d sub-sequences", num_trans), UVM_LOW)
      repeat (num_trans) begin
        run_child(vseq_names[$urandom_range(0, vseq_names.size() - 1)]);
        if (cfg.under_reset) break;
      end
    end
  join
endtask

task racl_ctrl_stress_all_vseq::run_child(string child_vseq_name);
  racl_ctrl_base_vseq child;
  `downcast(child, create_seq_by_name(child_vseq_name))
  child.set_sequencer(p_sequencer);

  // Decide whether the sub-sequence will apply a reset. If the current sequence is configured not
  // to apply a reset, don't do so in the child.
  child.do_apply_reset = do_apply_reset ? $urandom_range(0, 1) : 0;

  `DV_CHECK_RANDOMIZE_FATAL(child)
  child.start(p_sequencer);
endtask
