// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_fw_ov_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_fw_ov_vseq)

  `uvm_object_new

  push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH) m_rng_push_seq;

  int word_cnt;

  task body();
    super.body();

    // TODO: (Cleanup) do we want to change the cfg field "seed_cnt" to be more general?
    word_cnt = cfg.seed_cnt;

    // Create rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
                     create("m_rng_push_seq");

    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        do begin
          int available_words;
          // Wait for data to arrive for TL consumption via the ENTROPY_DATA register
          poll(.source(TlSrcObserveFIFO));
          // Read all currently available data (but no more than word_cnt)
          do_entropy_data_read(.source(TlSrcObserveFIFO), .max_bundles(word_cnt),
                               .bundles_found(available_words));
          // Update the count of remaining seeds to read
          word_cnt -= available_words;
        end while (word_cnt > 0);
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
      end
    join

  endtask : body

endclass : entropy_src_fw_ov_vseq
