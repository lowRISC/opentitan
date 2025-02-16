// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO(#26317):
//
//   This sequence doesn't really satisfy the cnt_rollover testpoint. The maximum prediv value is
//   (1<<32-1), which is very large! The code below actually constrains to a 16-bit prediv and also
//   overly constrains len and reps.
//
//   Unfortunately, the clk_cnt_q signal in pattgen_chan isn't actually exposed to other blocks. If
//   we want to work with large values, we'll probably need to force its value to "just below
//   prediv_q")

class pattgen_cnt_rollover_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_cnt_rollover_vseq)

  // Because the constraint on the sizes below is quite large, a simulation takes a long time.
  // Constrain num_trans to be reasonably small, in order to keep reasonable run times.
  extern constraint num_trans_c;

  extern function new(string name="");

  // This function is defined in pattgen_base_vseq, but we override it here to constrain the channel
  // configuration to be reasonably large.
  extern function pattgen_channel_cfg get_random_channel_config(uint channel);
endclass

constraint pattgen_cnt_rollover_vseq::num_trans_c {
  num_trans inside {[2 : 3]};
}

function pattgen_cnt_rollover_vseq::new(string name="");
  super.new(name);
  pattgen_max_dly = 0;
endfunction

function pattgen_channel_cfg pattgen_cnt_rollover_vseq::get_random_channel_config(uint channel);
  bit [1:0] is_max;
  pattgen_channel_cfg ch_cfg;
  ch_cfg = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg_%0d", channel));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ch_cfg,
    prediv dist {0 :/ 1, [1 : 'hfffe] :/ 1, 'hffff :/ 1};
    len    dist {0 :/ 1, [1 : 'he] :/ 1, 'hf :/ 1};
    reps   dist {0 :/ 1, [1 : 'h3e] :/ 1, 'h3f :/ 1};
    ((prediv+1) * (len+1) * (reps+1)) <= 'h1_0000;
    // dependent constraints
    solve len before data;
    data inside {[0 : (1 << (len + 1)) - 1]};
  )
  return ch_cfg;
endfunction
