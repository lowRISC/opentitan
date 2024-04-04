// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Count rollover test vseq
class pattgen_cnt_rollover_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_cnt_rollover_vseq)
  `uvm_object_new

  // reduce num_trans due to long running simulations
  constraint num_trans_c        { num_trans inside {[2 : 3]}; }
  // fast clear interrupt
  constraint clear_intr_dly_c   { clear_intr_dly == 0; }
  // fast stop/start channel
  constraint b2b_pattern_dly_c  { b2b_pattern_dly == 0; }

  // override this function for pattgen_cnt_rollover test
  function pattgen_channel_cfg get_random_channel_config(uint channel);
    bit [1:0] is_max;
    pattgen_channel_cfg ch_cfg;
    ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
      polarity dist {
        1'b0 :/ cfg.seq_cfg.pattgen_low_polarity_pct,
        1'b1 :/ (100 - cfg.seq_cfg.pattgen_low_polarity_pct)
      };
      prediv dist {0 :/ 1, [1 : 'hfffe] :/ 1, 'hffff :/ 1};
      len    dist {0 :/ 1, [1 : 'he] :/ 1, 'hf :/ 1};
      reps   dist {0 :/ 1, [1 : 'h3e] :/ 1, 'h3f :/ 1};
      ((prediv+1) * (len+1) * (reps+1)) <= 'h1_0000;
      // dependent constraints
      solve len before data;
      data inside {[0 : (1 << (len + 1)) - 1]};
    )
    return ch_cfg;
  endfunction : get_random_channel_config

endclass : pattgen_cnt_rollover_vseq
