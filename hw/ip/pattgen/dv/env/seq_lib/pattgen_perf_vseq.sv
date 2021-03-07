// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic perf test vseq
class pattgen_perf_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_perf_vseq)
  `uvm_object_new

  // reduce num_trans due to long running simulations
  constraint num_trans_c        { num_trans inside {[3:6]}; }
  // fast clear interrupt
  constraint clear_intr_dly_c   { clear_intr_dly == 0; }
  // fast stop/start channel
  constraint b2b_pattern_dly_c { b2b_pattern_dly == 0; }

  // override this function for pattgen_perf test
  function pattgen_channel_cfg get_random_channel_config(uint channel);
    pattgen_channel_cfg ch_cfg;
    ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
      ch_cfg.polarity dist {
        1'b0 :/ cfg.seq_cfg.pattgen_low_polarity_pct,
        1'b1 :/ (100 - cfg.seq_cfg.pattgen_low_polarity_pct)
      };
      ch_cfg.prediv dist {0 :/ 1, 1024 :/ 1};
      ch_cfg.len    dist {0 :/ 1, 1023 :/ 1};
      ch_cfg.reps   dist {0 :/ 1,   63 :/ 1};
      // dependent constraints
      solve ch_cfg.len before ch_cfg.data;
      ch_cfg.data inside {[0 : (1 << (ch_cfg.len + 1)) - 1]};
    )
    return ch_cfg;
  endfunction : get_random_channel_config

endclass : pattgen_perf_vseq
