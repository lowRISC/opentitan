// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A "combination vseq", which runs proper virtual sequences in a random order.

class ibex_icache_combo_vseq
  extends dv_base_vseq #(
    .CFG_T               (ibex_icache_env_cfg),
    .COV_T               (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T (ibex_icache_virtual_sequencer)
  );
  `uvm_object_utils(ibex_icache_combo_vseq)
  `uvm_object_new

  // The number of transactions across the combined sequences
  constraint num_trans_c { num_trans inside {[800:1000]}; }

  // The virtual sequences from which we'll build the test. Note that this doesn't contain
  // "ibex_icache_oldval_vseq": that sequence is for a specific test, which has a slightly different
  // checker.
  string seq_names[] = {"ibex_icache_back_line_vseq",
                        "ibex_icache_base_vseq", // for smoke test
                        "ibex_icache_caching_vseq",
                        "ibex_icache_ecc_vseq",
                        "ibex_icache_invalidation_vseq",
                        "ibex_icache_many_errors_vseq",
                        "ibex_icache_passthru_vseq"};

  // If this is set, occasionally reset the DUT and start a new sequence at a time that the core
  // sequence wouldn't normally expect.
  bit random_reset = 1'b0;

  // How many sequences have we executed so far?
  int unsigned seqs_so_far = 0;

  // The child (virtual) sequence
  ibex_icache_base_vseq child_seq;

  // The previous sequence that we ran.
  ibex_icache_base_vseq prev_seq = null;

  task body();
    int unsigned trans_so_far = 0;

    while (trans_so_far < num_trans) begin
      int unsigned seq_idx;
      uvm_sequence seq;
      int unsigned trans_now;
      bit          should_reset;

      seq_idx = $urandom_range(0, seq_names.size - 1);

      // Pick the number of transactions to run. We don't want too many, because the whole point is
      // that we're interested in the edges between sequences. Note that we don't bother to ensure
      // that trans_so_far + trans_now <= num_trans: it won't really matter if we overshoot by a
      // little.
      trans_now = $urandom_range(50, 100);

      // We don't need to reset if trans_so_far == 0 (because we did a reset before starting this
      // task). Otherwise, we always reset between sequences if random_reset is true. We'd always
      // need to if we killed the previous sequence, and it's easier not to bother tracking
      // properly. If random_reset is false (the usual back-to-back sequence test), we reset 1 time
      // in 2.
      if (trans_so_far == 0) should_reset = 1'b0;
      else if (random_reset) should_reset = 1'b1;
      else should_reset = $urandom_range(0, 1);

      // If we are resetting and trans_so_far > 0, we still have a (stopped) previous child
      // sequence. Tell it to reset its interfaces now, clearing signals, to make sure that no
      // sensitive input signal is high when the DUT goes into reset.
      if (trans_so_far > 0 && should_reset) begin
        child_seq.reset_ifs();
      end

      `uvm_info(`gfn,
                $sformatf("Running sequence '%s' (%0d transactions; reset=%0d).",
                          seq_names[seq_idx], trans_now, should_reset),
                UVM_HIGH)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(child_seq, seq)

      child_seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(child_seq)

      child_seq.num_trans = trans_now;
      child_seq.do_dut_init = should_reset;
      child_seq.prev_sequence = prev_seq;

      // The memory agent is careful to avoid consuming requests from its sequencer's request_fifo
      // until it has handled them. This is important if we're not resetting (it essentially allows
      // the sequence to change under the feet of the rest of the environment without it noticing),
      // but we need to make sure we discard any pending requests on an actual reset. Do that here.
      if (should_reset && seqs_so_far > 0) begin
        p_sequencer.mem_sequencer_h.request_fifo.flush();
      end

      run_sequence();

      prev_seq = child_seq;
      trans_so_far += trans_now;
      seqs_so_far  += 1;
    end
  endtask : body

  // Run a sequence. If random_reset = 0, this will run to completion. Otherwise, the sequence may
  // be stopped early.
  protected task run_sequence();
    int unsigned cycles_till_reset;
    bit          reached_timeout = 1'b0;

    if (!random_reset) begin
      child_seq.start(p_sequencer, this);
    end else begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cycles_till_reset,
                                         cycles_till_reset dist {
                                           [100:500]  :/ 1,
                                           [501:1000] :/ 4
                                         };)
      fork
        child_seq.start(p_sequencer, this);
        begin
          repeat (cycles_till_reset) @(cfg.clk_rst_vif.cb);
          reached_timeout = 1'b1;
        end
      join_any
    end

    if (reached_timeout) child_seq.kill();

    // Kill the timer process if it's still going.
    disable fork;
  endtask : run_sequence

endclass : ibex_icache_combo_vseq
