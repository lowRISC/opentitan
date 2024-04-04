// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Implements functional coverage for PATTGEN.
interface pattgen_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import pattgen_env_pkg::*;
  `include "dv_fcov_macros.svh"
  `include "uvm_macros.svh"

  parameter uint NO_DATA_BINS = 10;
  parameter uint NO_PREDIV_BINS = 10;
  parameter uint NO_REPS_BINS = 5;
  parameter uint NO_LEN_BINS = 5;

  `define CH0_PATH u_pattgen_core.chan0
  `define CH1_PATH u_pattgen_core.chan1

  wire rep_cnt_en_ch0 = `CH0_PATH.rep_cnt_en;
  wire rep_cnt_en_ch1 = `CH1_PATH.rep_cnt_en;
  wire len_q0 = `CH0_PATH.len_q;
  wire len_q1 = `CH1_PATH.len_q;
  wire reps_q0 = `CH0_PATH.reps_q;
  wire reps_q1 = `CH1_PATH.reps_q;
  wire clk_cnt_q0 = `CH0_PATH.clk_cnt_q;
  wire clk_cnt_q1 = `CH1_PATH.clk_cnt_q;
  wire bit_cnt_q0 = `CH0_PATH.bit_cnt_q;
  wire bit_cnt_q1 = `CH1_PATH.bit_cnt_q;
  wire rep_cnt_q0 = `CH0_PATH.rep_cnt_q;
  wire rep_cnt_q1 = `CH1_PATH.rep_cnt_q;
  wire prediv_q0 = `CH0_PATH.prediv_q;
  wire prediv_q1 = `CH1_PATH.prediv_q;


  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov
  //must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup ctrl_cg @(posedge clk_i);

    option.name         = "ctrl_cg";
    option.comment      = "Enable and polarity coverage";

    cp_enable_ch0: coverpoint `CH0_PATH.enable;
    cp_enable_ch1: coverpoint `CH1_PATH.enable;
    cp_polarity_ch0: coverpoint `CH0_PATH.polarity_q;
    cp_polarity_ch1: coverpoint `CH1_PATH.polarity_q;

    cross_contr: cross cp_enable_ch0, cp_enable_ch1,
                       cp_polarity_ch0, cp_polarity_ch1;

  endgroup : ctrl_cg

 `DV_FCOV_INSTANTIATE_CG(ctrl_cg, en_full_cov)

    wire ch0_cnt_match_prediv = (prediv_q0 == clk_cnt_q0);
    wire ch0_cnt_reset = (clk_cnt_q0 == 0);
    wire ch0_cnt_match_len = (len_q0 == bit_cnt_q0);
    wire ch0_cnt_len_reset = (bit_cnt_q0 == 0);
    wire ch0_cnt_match_reps = (reps_q0 == rep_cnt_q0);
    wire ch0_cnt_reset_reps = (rep_cnt_q0 == 0);

    wire ch1_cnt_match_prediv = (prediv_q1 == clk_cnt_q1);
    wire ch1_cnt_reset = (clk_cnt_q1 == 0);
    wire ch1_cnt_match_len = (len_q1 == bit_cnt_q1);
    wire ch1_cnt_len_reset = (bit_cnt_q1 == 0);
    wire ch1_cnt_match_reps = (reps_q1 == rep_cnt_q1);
    wire ch1_cnt_reset_reps = (rep_cnt_q1 == 0);

  covergroup pattgen_ch0_cnt_reset_cg @(posedge clk_i);

    option.name         = "ch0_cnt_reset_cg";
    option.comment      = "Counters reset after match";

    cp_reps_trans_ch0: coverpoint {ch0_cnt_match_reps, ch0_cnt_reset_reps, rep_cnt_en_ch0}{
      bins trans2Zero_reps = (3'b100 => 3'b101 => 3'b010);
      bins others = default;
    }

    cp_reps_reset_trans_ch0: coverpoint {ch0_cnt_match_reps, ch0_cnt_reset_reps}{
      bins trans2Zero_reps = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_len_reset_trans_ch0: coverpoint {ch0_cnt_match_len, ch0_cnt_len_reset}{
      bins trans2Zero_len = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_prediv_reset_trans_ch0: coverpoint {ch0_cnt_match_prediv, ch0_cnt_reset}{
      bins trans2Zero_prediv = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_cross_reps_len_prediv: cross cp_reps_reset_trans_ch0, cp_len_reset_trans_ch0,
                                    cp_len_reset_trans_ch0;

    cp_match_reps_tr_ch0: coverpoint {ch0_cnt_match_reps}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

    cp_reset_reps_tr_ch0: coverpoint {ch0_cnt_reset_reps}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

    cp_rep_cnt_en_tr_ch0: coverpoint {rep_cnt_en_ch0}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

  endgroup : pattgen_ch0_cnt_reset_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_ch0_cnt_reset_cg, en_full_cov)

  covergroup pattgen_ch1_cnt_reset_cg @(posedge clk_i);

    option.name         = "ch1_cnt_reset_cg";
    option.comment      = "Counters reset after match";

    cp_reps_trans_ch1: coverpoint {ch1_cnt_match_reps, ch1_cnt_reset_reps, rep_cnt_en_ch1}{
      bins trans2Zero_reps = (3'b100 => 3'b101 => 3'b010);
      bins others = default;
    }

    cp_reps_reset_trans_ch1: coverpoint {ch1_cnt_match_reps, ch1_cnt_reset_reps}{
      bins trans2Zero_reps = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_len_reset_trans_ch1: coverpoint {ch1_cnt_match_len, ch1_cnt_len_reset}{
      bins trans2Zero_len = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_prediv_reset_trans_ch1: coverpoint {ch1_cnt_match_prediv, ch1_cnt_reset}{
      bins trans2Zero_prediv = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_cross_reps_len_prediv_ch1: cross cp_reps_reset_trans_ch1, cp_len_reset_trans_ch1,
                                    cp_len_reset_trans_ch1;

    cp_match_reps_tr_ch1: coverpoint {ch1_cnt_match_reps}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

    cp_reset_reps_tr_ch1: coverpoint {ch1_cnt_reset_reps}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

    cp_rep_cnt_en_tr_ch1: coverpoint {rep_cnt_en_ch1}{
      bins zero2one = (1'b0 => 1'b1);
      bins one2zero = (1'b1 => 1'b0);
    }

  endgroup : pattgen_ch1_cnt_reset_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_ch1_cnt_reset_cg, en_full_cov)

  covergroup inter_cg @(posedge clk_i);

    option.name         = "inter_cg";
    option.comment      = "Interrupts checking";

    cp_intr_enab_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_enable.done_ch0.q;
    cp_intr_state_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_state.done_ch0.q;
    cp_intr_test_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_test.done_ch0.q;

    intr_cross: cross cp_intr_enab_ch0, cp_intr_state_ch0, cp_intr_test_ch0;

  endgroup : inter_cg

 `DV_FCOV_INSTANTIATE_CG(inter_cg, en_full_cov)

  //NOTE upper and lower parts of data cannot be accessed with CHAN* macro
  //because channels receive merged 64 bit data.

  covergroup pattgen_data_ch0_0_cg @(posedge clk_i);

    option.name         = "pattgen_data_ch0_0_cg";
    option.comment      = "Data coverage in LSB Chan0";

    cp_data_ch00: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[31:0]}{
      bins maxim = {DataMax};
      bins mid[NO_DATA_BINS] = {[DataMin + 1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : pattgen_data_ch0_0_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_data_ch0_0_cg, en_full_cov)

  covergroup pattgen_data_ch0_1_cg @(posedge clk_i);

    option.name         = "pattgen_data_ch0_1_cg";
    option.comment      = "Data coverage in MSB Chan0";

    cp_data_ch01: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[63:32]}{
      bins maxim = {DataMax};
      bins mid[NO_DATA_BINS] = {[DataMin +1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : pattgen_data_ch0_1_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_data_ch0_1_cg, en_full_cov)

  covergroup pattgen_data_ch1_0_cg @(posedge clk_i);

    option.name         = "pattgen_data_ch1_0_cg";
    option.comment      = "Data coverage in LSB Chan1";

    cp_data_ch10: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[31:0]}{
      bins maxim = {DataMax};
      bins mid[NO_DATA_BINS] = {[DataMin +1 : DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : pattgen_data_ch1_0_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_data_ch1_0_cg, en_full_cov)

  covergroup pattgen_data_ch1_1_cg @(posedge clk_i);

    option.name         = "pattgen_data_ch1_1_cg";
    option.comment      = "Data coverage in MSB Chan1";

    cp_data_ch11: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[63:32]}{
      bins maxim = {DataMax};
      bins mid[NO_DATA_BINS] = {[DataMin + 1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : pattgen_data_ch1_1_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_data_ch1_1_cg, en_full_cov)

  covergroup pattgen_prediv_ch0_cg @(posedge clk_i);

    option.name         = "pattgen_prediv_ch0_cg";
    option.comment      = "Chan0 Pre-divide clock coefficient coverage";

    cp_prediv_ch0: coverpoint {prediv_q0}{
      bins maxim = {PredivMaxValue};
      bins mid[NO_PREDIV_BINS] = {[PredivMinValue + 1:PredivMaxValue - 1]};
      bins minim = {PredivMinValue};
    }

  endgroup : pattgen_prediv_ch0_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_prediv_ch0_cg, en_full_cov)

  covergroup pattgen_prediv_ch1_cg @(posedge clk_i);

    option.name         = "pattgen_prediv_ch1_cg";
    option.comment      = "Chan1 Pre-divide clock coefficient coverage";

    cp_prediv_ch1: coverpoint {prediv_q1}{
      bins maxim = {PredivMaxValue};
      bins mid[NO_PREDIV_BINS] = {[PredivMinValue + 1:PredivMaxValue - 1]};
      bins minim = {PredivMinValue};
    }

  endgroup : pattgen_prediv_ch1_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_prediv_ch1_cg, en_full_cov)

  covergroup pattgen_reps_ch0_cg @(posedge clk_i);

    option.name         = "pattgen_reps_ch0_cg";
    option.comment      = "Chan0 repetition coefficient coverage";

    cp_reps_ch0: coverpoint {reps_q0}{
      bins maxim = {RepsMaxValue};
      bins mid[NO_REPS_BINS] = {[RepsMinValue + 1:RepsMaxValue - 1]};
      bins minim = {RepsMinValue};
    }

  endgroup : pattgen_reps_ch0_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_reps_ch0_cg, en_full_cov)

  covergroup pattgen_reps_ch1_cg @(posedge clk_i);

    option.name         = "pattgen_reps_ch1_cg";
    option.comment      = "Chan1 repetition coefficient coverage";

    cp_reps_ch1: coverpoint {reps_q1}{
      bins maxim_1 = {RepsMaxValue};
      bins mid_1[NO_REPS_BINS] = {[RepsMinValue + 1:RepsMaxValue - 1]};
      bins minim_1 = {RepsMinValue};

    }

  endgroup : pattgen_reps_ch1_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_reps_ch1_cg, en_full_cov)

  covergroup pattgen_len_ch0_cg @(posedge clk_i);

    option.name         = "pattgen_len_ch0_cg";
    option.comment      = "Chan0 length coverage";

    cp_len_ch0: coverpoint {len_q0}{
      bins maxim = {LenMaxValue};
      bins middle[NO_LEN_BINS] = {[LenMinValue + 1:LenMaxValue - 1]};
      bins minim = {LenMinValue};
    }

  endgroup : pattgen_len_ch0_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_len_ch0_cg, en_full_cov)

  covergroup pattgen_len_ch1_cg @(posedge clk_i);

    option.name         = "pattgen_len_ch1_cg";
    option.comment      = "Chan1 length coverage";

    cp_len_ch1: coverpoint {len_q1}{
      bins maxim_1 = {LenMaxValue};
      bins middle_1[NO_LEN_BINS] = {[LenMinValue + 1:LenMaxValue - 1]};
      bins minim_1 = {LenMinValue};
    }

  endgroup : pattgen_len_ch1_cg

 `DV_FCOV_INSTANTIATE_CG(pattgen_len_ch1_cg, en_full_cov)

 covergroup roll_cg @(posedge clk_i);

    option.name         = "roll_cg";
    option.comment      = "Cover max/min values of counters";

    cp_prediv_cnt_ch0: coverpoint {prediv_q0}{
      bins maxim_0 = {'hffffffff};
      bins mid_range_0[NO_PREDIV_BINS] = {[1:'hfffffffe]};
      bins minim_0 = {0};
    }

    cp_prediv_cnt_ch1: coverpoint {prediv_q1}{
      bins maxim_1 = {'hffffffff};
      bins mid_range_1[NO_PREDIV_BINS] = {[1:'hfffffffe]};
      bins minim_1 = {0};
    }

    cp_len_cnt_ch0: coverpoint {len_q0}{
      bins maxim_0 = {'h3f};
      bins mid_range_0[NO_LEN_BINS] = {[1:'h3e]};
      bins minim_0 = {0};
    }

    cp_len_cnt_ch1: coverpoint {len_q1}{
      bins maxim_1 = {'h3f};
      bins mid_range_1[NO_LEN_BINS] = {[1:'h3e]};
      bins minim_1 = {0};
    }

    cp_reps_cnt_ch0: coverpoint {reps_q0}{
      bins maxim_0 = {'h3ff};
      bins mid_range_0[NO_REPS_BINS] = {[1:'h3fe]};
      bins minim_0 = {0};
    }

    cp_reps_cnt_ch1: coverpoint {reps_q1}{
      bins maxim_1 = {'h3ff};
      bins mid_range_1[NO_REPS_BINS] = {[1:'h3fe]};
      bins minim_1 = {0};
    }

    cross_rollover_cnt_ch0: cross cp_prediv_cnt_ch0, cp_len_cnt_ch0, cp_reps_cnt_ch0;
    cross_rollover_cnt_ch1: cross cp_prediv_cnt_ch1, cp_len_cnt_ch1, cp_reps_cnt_ch1;

  endgroup : roll_cg

 `DV_FCOV_INSTANTIATE_CG(roll_cg, en_full_cov)

  covergroup pattgen_op_cg @(posedge clk_i);
    option.name         = "pattgen_op_cg";
    option.comment      = "Chan0 and Chan1 interrupt done and event done coverage";

    cp_intr_done_ch0_o: coverpoint u_pattgen_core.intr_done_ch0_o;
    cp_intr_done_ch1_o: coverpoint u_pattgen_core.intr_done_ch1_o;
    cp_event_done_ch0: coverpoint  `CH0_PATH.event_done_o;
    cp_event_done_ch1: coverpoint  `CH1_PATH.event_done_o;

  endgroup : pattgen_op_cg

  `DV_FCOV_INSTANTIATE_CG(pattgen_op_cg, en_full_cov)

endinterface : pattgen_cov_if
