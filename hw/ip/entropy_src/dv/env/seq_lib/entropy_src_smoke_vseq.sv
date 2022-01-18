// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_smoke_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_smoke_vseq)

  `uvm_object_new

  int rng_count = 0;
  int offset = 0;
  int seed_cnt;

  push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH) m_rng_push_seq;

  task body();
    super.body();

    seed_cnt = cfg.seed_cnt;

    // Create rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
                     create("m_rng_push_seq");


    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        do begin
          int available_seeds;
          // Wait for data to arrive for TL consumption via the ENTROPY_DATA register
          csr_spinwait(.ptr(ral.intr_state.es_entropy_valid), .exp_data(1'b1));
          // Read all currently available data (but no more than seed_cnt)
          do_entropy_data_read(.max_seeds(seed_cnt), .seeds_found(available_seeds));
          // Update the count of remaining seeds to read
          seed_cnt -= available_seeds;
        end while (seed_cnt > 0);
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
      end
    join

  endtask : body

endclass : entropy_src_smoke_vseq
