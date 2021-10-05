// Copyright lowRISC contributors.
// Licensed under the Apache License,
// SPDX-License-Identifier: Apache-2.0

// Implements functional coverage for PATTGEN.
interface pattgen_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"
  `include "uvm_macros.svh"

  `define CH0_PATH u_pattgen_core.chan0
  `define CH1_PATH u_pattgen_core.chan1

  localparam uint DataMax = 32'hffffffff;
  localparam uint DataMin = 32'hfffffffb;
  localparam uint DataMax_low = 20;
  localparam uint DataMin_low = 0;
  localparam uint PredivMaxValue = 32'hffffffff;
  localparam uint PredivMinValue = 32'hfffffffc;
  localparam uint RepsMaxValue = 10'h3ff;
  localparam uint RepsMinValue = 10'h3fc;
  localparam uint LenMaxValue = 10'h3f;
  localparam uint LenMinValue = 10'h3c;

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

  covergroup contr_cg @(posedge clk_i);

    option.name         = "contr_cg";
    option.comment      = "Enable and polarity coverage";

    cp_enable_ch0: coverpoint `CH0_PATH.enable;
    cp_enable_ch1: coverpoint `CH1_PATH.enable;
    cp_polarity_ch0: coverpoint `CH0_PATH.polarity_q;
    cp_polarity_ch1: coverpoint `CH1_PATH.polarity_q;

    cross_contr: cross cp_enable_ch0, cp_enable_ch1,
                       cp_polarity_ch0, cp_polarity_ch1;

  endgroup : contr_cg

 `DV_FCOV_INSTANTIATE_CG(contr_cg, en_full_cov)

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

  covergroup roll_cg @(posedge clk_i);

    option.name         = "roll_cg";
    option.comment      = "Counters reset after match";

    cp_reps_trans_ch0: coverpoint {ch0_cnt_match_reps, ch0_cnt_reset_reps, rep_cnt_en_ch0}{
      bins trans2Zero_reps[] = (3'b100 => 3'b101 => 3'b010);
      bins others = default;
    }

    cp_reps_reset_trans_ch0: coverpoint {ch0_cnt_match_reps, ch0_cnt_reset_reps}{
      bins trans2Zero_reps[] = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_len_reset_trans_ch0: coverpoint {ch0_cnt_match_len, ch0_cnt_len_reset}{
      bins trans2Zero_len[] = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_prediv_reset_trans_ch0: coverpoint {ch0_cnt_match_prediv, ch0_cnt_reset}{
      bins trans2Zero_prediv[] = (2'b10 => 2'b01);
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

  endgroup : roll_cg

 `DV_FCOV_INSTANTIATE_CG(roll_cg, en_full_cov)

  covergroup roll_cg_ch1 @(posedge clk_i);

    option.name         = "roll_cg_ch1";
    option.comment      = "Counters reset after match";

    cp_reps_trans_ch1: coverpoint {ch1_cnt_match_reps, ch1_cnt_reset_reps, rep_cnt_en_ch1}{
      bins trans2Zero_reps[] = (3'b100 => 3'b101 => 3'b010);
      bins others = default;
    }

    cp_reps_reset_trans_ch1: coverpoint {ch1_cnt_match_reps, ch1_cnt_reset_reps}{
      bins trans2Zero_reps[] = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_len_reset_trans_ch1: coverpoint {ch1_cnt_match_len, ch1_cnt_len_reset}{
      bins trans2Zero_len[] = (2'b10 => 2'b01);
      bins others = default;
    }

    cp_prediv_reset_trans_ch1: coverpoint {ch1_cnt_match_prediv, ch1_cnt_reset}{
      bins trans2Zero_prediv[] = (2'b10 => 2'b01);
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

  endgroup : roll_cg_ch1

 `DV_FCOV_INSTANTIATE_CG(roll_cg_ch1, en_full_cov)

  covergroup intr_cg @(posedge clk_i);

    option.name         = "intr_cg";
    option.comment      = "Interrupts checking";

    cp_intr_enab_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_enable.done_ch0.q;
    cp_intr_state_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_state.done_ch0.q;
    cp_intr_test_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_test.done_ch0.q;

    intr_cross: cross cp_intr_enab_ch0, cp_intr_state_ch0, cp_intr_test_ch0;


  endgroup : intr_cg

 `DV_FCOV_INSTANTIATE_CG(intr_cg, en_full_cov)

  //NOTE upper and lower parts of data cannot be accessed with CHAN* macro
  //because channels receive merged 64 bit data.

  covergroup ch0_data_word0_cg @(posedge clk_i);

    option.name         = "ch0_data_word0_cg";
    option.comment      = "Data coverage in LSB Chan0";

    cp_data_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[31:0]}{
      bins maxim = {DataMax};
      bins mid[] = {[DataMin + 1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : ch0_data_word0_cg

 `DV_FCOV_INSTANTIATE_CG(ch0_data_word0_cg, en_full_cov)

  covergroup ch0_data_word1_cg @(posedge clk_i);

    option.name         = "ch0_data_word1_cg";
    option.comment      = "Data coverage in MSB Chan0";

    cp_data_ch1: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[63:32]}{
      bins maxim = {DataMax};
      bins mid[] = {[DataMin +1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : ch0_data_word1_cg

 `DV_FCOV_INSTANTIATE_CG(ch0_data_word1_cg, en_full_cov)

  covergroup ch1_data_word0_cg @(posedge clk_i);

    option.name         = "ch1_data_word0_cg";
    option.comment      = "Data coverage in LSB Chan1";

    cp_data_ch10: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[31:0]}{
      bins maxim = {DataMax};
      bins mid[] = {[DataMin +1 : DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : ch1_data_word0_cg

 `DV_FCOV_INSTANTIATE_CG(ch1_data_word0_cg, en_full_cov)

  covergroup ch1_data_word1_cg @(posedge clk_i);

    option.name         = "ch1_data_word1_cg";
    option.comment      = "Data coverage in MSB Chan1";

    cp_data_ch1: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[63:32]}{
      bins maxim = {DataMax};
      bins mid[] = {[DataMin + 1:DataMax - 1]};
      bins minim = {DataMin};
    }

  endgroup : ch1_data_word1_cg

 `DV_FCOV_INSTANTIATE_CG(ch1_data_word1_cg, en_full_cov)

  covergroup ch0_prediv_cg @(posedge clk_i);

    option.name         = "ch0_prediv_cg";
    option.comment      = "Chan0 Pre-divide clock coefficient coverage";

    cp_prediv_ch0: coverpoint {prediv_q0}{
      bins maxim = {PredivMaxValue};
      bins mid[] = {[PredivMinValue + 1:PredivMaxValue - 1]};
      bins minim = {PredivMinValue};
    }

  endgroup : ch0_prediv_cg

 `DV_FCOV_INSTANTIATE_CG(ch0_prediv_cg, en_full_cov)

  covergroup ch1_prediv_cg @(posedge clk_i);

    option.name         = "ch1_prediv_cg";
    option.comment      = "Chan1 Pre-divide clock coefficient coverage";

    cp_prediv_ch1: coverpoint {prediv_q1}{
      bins maxim = {PredivMaxValue};
      bins mid[] = {[PredivMinValue + 1:PredivMaxValue - 1]};
      bins minim = {PredivMinValue};
    }

  endgroup : ch1_prediv_cg

 `DV_FCOV_INSTANTIATE_CG(ch1_prediv_cg, en_full_cov)

  covergroup ch0_reps_cg @(posedge clk_i);

    option.name         = "ch0_reps_cg";
    option.comment      = "Chan0 repetition coefficient coverage";

    cp_reps_ch0: coverpoint {reps_q0}{
      bins maxim = {RepsMaxValue};
      bins mid[] = {[RepsMinValue + 1:RepsMaxValue - 1]};
      bins minim = {RepsMinValue};
    }

  endgroup : ch0_reps_cg

 `DV_FCOV_INSTANTIATE_CG(ch0_reps_cg, en_full_cov)

  covergroup ch1_reps_cg @(posedge clk_i);

    option.name         = "ch1_reps_cg";
    option.comment      = "Chan1 repetition coefficient coverage";

    cp_reps_ch1: coverpoint {reps_q1}{
      bins maxim_1 = {RepsMaxValue};
      bins mid_1[] = {[RepsMinValue + 1:RepsMaxValue - 1]};
      bins minim_1 = {RepsMinValue};

    }

  endgroup : ch1_reps_cg

 `DV_FCOV_INSTANTIATE_CG(ch1_reps_cg, en_full_cov)

  covergroup ch0_len_cg @(posedge clk_i);

    option.name         = "ch0_len_cg";
    option.comment      = "Chan0 length coverage";

    cp_len_ch0: coverpoint {len_q0}{
      bins maxim = {LenMaxValue};
      bins middle[] = {[LenMinValue + 1:LenMaxValue - 1]};
      bins minim = {LenMinValue};
    }

  endgroup : ch0_len_cg

 `DV_FCOV_INSTANTIATE_CG(ch0_len_cg, en_full_cov)

  covergroup ch1_len_cg @(posedge clk_i);

    option.name         = "ch1_len_cg";
    option.comment      = "Chan1 length coverage";

    cp_len_ch1: coverpoint {len_q1}{
      bins maxim_1 = {LenMaxValue};
      bins middle_1[] = {[LenMinValue + 1:LenMaxValue - 1]};
      bins minim_1 = {LenMinValue};

    }

  endgroup : ch1_len_cg

 `DV_FCOV_INSTANTIATE_CG(ch1_len_cg, en_full_cov)

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
