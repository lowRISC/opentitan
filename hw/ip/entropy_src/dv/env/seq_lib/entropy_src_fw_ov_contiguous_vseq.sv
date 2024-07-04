// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_fw_ov_contiguous_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_fw_ov_contiguous_vseq)

  `uvm_object_new

  push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH) m_rng_push_seq;

  int bundle_cnt;

  task body();

    bundle_cnt = cfg.fw_ov_rd_cnt/cfg.dut_cfg.observe_fifo_thresh + 1;

    // Create rng host sequence
    m_rng_push_seq = push_pull_indefinite_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
                     create("m_rng_push_seq");

    fork
      m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
      begin
        int available_bundles;
        bit [TL_DW-1:0] observe_fifo_depth;
        do begin
          // Wait for data to arrive for TL consumption via the ENTROPY_DATA register
          poll(.source(TlSrcObserveFIFO));
          // Read all currently available data (but no more than bundle_cnt)
          do_entropy_data_read(.source(TlSrcObserveFIFO), .max_bundles(bundle_cnt),
                               .bundles_found(available_bundles), .check_overflow(1));
          // Update the count of remaining seeds to read
          bundle_cnt -= available_bundles;
        end while (bundle_cnt > 0);
        csr_rd(.ptr(ral.observe_fifo_depth.observe_fifo_depth), .value(observe_fifo_depth),
                .blocking(1'b1));
        m_rng_push_seq.stop(.hard(0));
        m_rng_push_seq.wait_for_sequence_state(UVM_FINISHED);
      end
    join

  endtask : body

endclass : entropy_src_fw_ov_contiguous_vseq
