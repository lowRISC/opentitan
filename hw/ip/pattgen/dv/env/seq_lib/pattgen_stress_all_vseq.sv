// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all pattgen seqs (except below vseqs) in one seq to run sequentially
// 1. override_vseq requires scb and monitor to be disabled
// 1. csr seq, which requires scb to be disabled
class pattgen_stress_all_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_stress_all_vseq)

  `uvm_object_new

  local string str, seq_name;
  local int    seq_run_hist[string];

  string seq_names[] = {
    "pattgen_common_vseq",      // for intr_test
    "pattgen_smoke_vseq",
    "pattgen_perf_vseq",
    "pattgen_error_vseq"
  };

  virtual task body();

    `uvm_info(`gfn, "\n=> start pattgen_stress_all_vseq", UVM_LOW)
    print_seq_names(seq_names);
    for (int i = 1; i <= seq_names.size(); i++) begin
      seq_run_hist[seq_names[i-1]] = 0;
    end

    for (int i = 1; i <= num_runs; i++) begin
      uvm_sequence       seq;
      pattgen_base_vseq  pattgen_vseq;
      uint               seq_idx = $urandom_range(0, seq_names.size() - 1);

      seq_name = seq_names[seq_idx];
      `uvm_info(`gfn, $sformatf("\n\n=> start stressing vseq %s (%0d/%0d)",
          seq_name, i, num_runs), UVM_LOW)
      seq = create_seq_by_name(seq_name);
      `downcast(pattgen_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) begin
        pattgen_vseq.do_apply_reset = $urandom_range(0, 1);
        if (pattgen_vseq.do_apply_reset) begin
          `uvm_info(`gfn, "\n  *reset is randomly issued with stress_test", UVM_LOW)
        end
      end else begin
        pattgen_vseq.do_apply_reset = 0;
        `uvm_info(`gfn, "\n  *upper_seq may drive reset thus not issue reset", UVM_DEBUG)
      end

      pattgen_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(pattgen_vseq)
      case (seq_name)
        "pattgen_common_vseq": begin
          pattgen_common_vseq common_vseq;
          `downcast(common_vseq, pattgen_vseq);
          common_vseq.common_seq_type = "intr_test";
          cfg.en_scb = 1'b0;
        end
        default: begin
          cfg.en_scb = 1'b1;
        end
      endcase
      // run vseq
      pattgen_vseq.start(p_sequencer);
      seq_run_hist[seq_name]++;
      `uvm_info(`gfn, $sformatf("\n  end stressing vseq %s", seq_name), UVM_LOW)
    end
    wait_host_for_idle();
    `uvm_info(`gfn, "\n=> end of pattgen_stress_all_vseq", UVM_LOW)

    // get the histogram of vseq running
    str = {str, "\n\n=> vseq run histogram:"};
    for (int i = 0; i < seq_names.size(); i++) begin
      seq_name = seq_names[i];
      str = {str, $sformatf("\n  %-25s  %2d / %2d", seq_name, seq_run_hist[seq_name], num_runs)};
    end
    `uvm_info(`gfn, $sformatf("%s\n", str), UVM_LOW)
  endtask : body

  virtual function void print_seq_names(const ref string seq_names[]);
    string str;

    `uvm_info(`gfn, $sformatf("\n  list of %0d vseqs are stressed", seq_names.size()), UVM_LOW)
    for (int i = 1; i <= seq_names.size(); i++) begin
      str = {str, $sformatf("\n    %s", seq_names[i-1])};
    end
    `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
  endfunction : print_seq_names

endclass : pattgen_stress_all_vseq
