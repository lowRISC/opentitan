// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Implements functional coverage for PATTGEN.
interface pattgen_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"
  `include "uvm_macros.svh"

  `define CH0_PATH u_pattgen_core.chan0;
  `define CH1_PATH u_pattgen_core.chan1;

  bit [63:0] ch0_data;
  bit [63:0] ch1_data;
  bit position;

  assign ch0_data[63:0] = {u_pattgen_core.ch0_ctrl.data[63:32],
  u_pattgen_core.ch0_ctrl.data[31:0]};
  assign ch1_data[63:0] = {u_pattgen_core.ch1_ctrl.data[63:32],
  u_pattgen_core.ch1_ctrl.data[31:0]};

  parameter WIDTH = 32'hffffffff;
  uint data_max = 32'hffffffff;
  uint data_min = 32'hfffffffb;
  uint prediv_max_value = 32'hfffffff;
  uint prediv_min_value = 32'hffffffc;
  uint reps_max_value = 10'h3ff;
  uint reps_min_value = 10'h3fc;
  uint len_max_value = 10'h3f;
  uint len_min_value = 10'h3c;
  parameter int CH_WIDTH = 64;
  parameter int REP_MAX = 9'h1FF;
  parameter int LENGTH_MAX = 6'h3F;

  bit ch0_perf, ch1_perf;
  assign ch0_perf = {u_pattgen_core.ch0_ctrl.len,
                     u_pattgen_core.ch0_ctrl.reps,
                     u_pattgen_core.ch0_ctrl.prediv} == 'h0;
  assign ch1_perf = {u_pattgen_core.ch1_ctrl.len,
                     u_pattgen_core.ch1_ctrl.reps,
                     u_pattgen_core.ch1_ctrl.prediv} == 'h0;

  bit enab0 = CH0_PATH.enable;
  bit enab1 = CH1_PATH.enable;
  bit complete_q0 = CH0_PATH.complete_q;
  bit complete_q1 = CH1_PATH.complete_q;
  bit len_q0 = CH0_PATH.len_q;
  bit pcl_int_d0 = CH0_PATH.pcl_int_d;
  bit pcl_int_d1 = CH1_PATH.pcl_int_d;
  bit clk_cnt_d0 = CH0_PATH.clk_cnt_d;
  bit clk_cnt_d1 = CH1_PATH.clk_cnt_d;
  bit bit_cnt_d0 = CH0_PATH.bit_cnt_d;
  bit bit_cnt_d1 = CH1_PATH.bit_cnt_d;
  bit reps_q0 = CH0_PATH.reps_q;
  bit rep_cnt_d0 = CH0_PATH.rep_cnt_d;
  bit rep_cnt_d1 = CH1_PATH.rep_cnt_d;
  bit complete_d0 = CH0_PATH.complete_d;
  bit complete_d1 = CH1_PATH.complete_d;
  bit clk_cnt_q0 = CH0_PATH.clk_cnt_q;
  bit bit_cnt_q0 = CH0_PATH.bit_cnt_q;
  bit rep_cnt_q0 = CH0_PATH.rep_cnt_q;
  bit clk_cnt_q1 = CH1_PATH.clk_cnt_q;
  bit prediv_q0 = CH0_PATH.prediv_q;
  bit prediv_q1 = CH1_PATH.prediv_q;
  bit pcl_int_q0 = CH0_PATH.pcl_int_q;
  bit rst_ni;

  bit cnt_q0_match = {clk_cnt_q0 == prediv_q0};
  bit cnt_q1_match = {clk_cnt_q1 == prediv_q1};
  bit prediv_q0_match = {prediv_q0 == WIDTH};
  bit ch0_sig = {complete_q0, pcl_int_d0, cnt_q0_match,
  clk_cnt_q0, bit_cnt_q0, rep_cnt_q0};
  bit ch1_sig = {complete_q1, pcl_int_d1, cnt_q1_match};
  bit ch01_sig = {complete_q0, complete_q1,
  pcl_int_d0, pcl_int_d1, cnt_q0_match, cnt_q1_match};

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov
  //must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup contr_cg @(posedge clk_i);

    option.name         = "contr_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_enable_ch0: coverpoint enab0;
    cp_enable_ch1: coverpoint enab1;
    cp_polarity_ch0: coverpoint u_pattgen_core.ch0_ctrl.polarity;
    cp_polarity_ch1: coverpoint u_pattgen_core.ch1_ctrl.polarity;

    cross_contr: cross cp_enable_ch0, cp_enable_ch1,
                       cp_polarity_ch0, cp_polarity_ch1;


  endgroup : contr_cg

 `DV_FCOV_INSTANTIATE_CG(contr_cg, en_full_cov)

    bit ch0_cnt_match_prediv = (u_pattgen_core.ch0_ctrl.prediv == CH0_PATH.clk_cnt_q);
    bit ch0_cnt_is_reset = (CH0_PATH.clk_cnt_q == 0);

  covergroup roll_cg @(posedge clk_i);

    option.name         = "roll_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_prediv0_match: coverpoint match;

    cp_clk_cnt_q_trans: coverpoint {match, reset}{
    bins from_cnt_match_to_zero = (2'b10 => 2'b00 =>2'b01);
    bins others = default;
    }


  endgroup : roll_cg

 `DV_FCOV_INSTANTIATE_CG(roll_cg, en_full_cov)

  covergroup intr_cg @(posedge clk_i);

    option.name         = "intr_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_intr_enab_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_enable.done_ch0.q;
    cp_intr_state_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_state.done_ch0.q;
    cp_intr_test_ch0: coverpoint
    u_pattgen_core.reg2hw.intr_test.done_ch0.q;

    intr_cross: cross cp_intr_enab_ch0, cp_intr_state_ch0, cp_intr_test_ch0;


  endgroup : intr_cg

 `DV_FCOV_INSTANTIATE_CG(intr_cg, en_full_cov)

    bit data_match = (tb.dut.u_pattgen_core.ch0_ctrl.data[31:0] == data_max);

  covergroup data_00_cg @(posedge clk_i);

    option.name         = "data_00_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_data_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[31:0]}{
      bins max = data_max;
      bins mid[] = {[data_min:data_max]};
      bins min = data_min;
    }

  endgroup : data_00_cg

 `DV_FCOV_INSTANTIATE_CG(data_00_cg, en_full_cov)

  covergroup data_01_cg @(posedge clk_i);

    option.name         = "data_01_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_data_ch1: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[63:32]}{
      bins max = data_max;
      bins mid[] = {[data_min:data_max]};
      bins min = data_min;
    }

  endgroup : data_01_cg

 `DV_FCOV_INSTANTIATE_CG(data_01_cg, en_full_cov)


  covergroup prediv_cg @(posedge clk_i);

    option.name         = "prediv_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_prediv_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.prediv}{
      bins max = prediv_max_value;
      bins mid[] = {[prediv_min_value:prediv_max_value]};
      bins min = prediv_min_value;
    }

  endgroup : prediv_cg


 `DV_FCOV_INSTANTIATE_CG(prediv_cg, en_full_cov)

  covergroup prediv_1_cg @(posedge clk_i);

    option.name         = "prediv_1_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_prediv_ch1: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.prediv}{
      bins max = prediv_max_value;
      bins mid[] = {[prediv_min_value:prediv_max_value]};
      bins min = prediv_min_value;
    }

  endgroup : prediv_1_cg

 `DV_FCOV_INSTANTIATE_CG(prediv_1_cg, en_full_cov)

  covergroup reps_cg @(posedge clk_i);

    option.name         = "reps_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_reps_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.reps}{
      bins max = reps_max_value;
      bins mid[] = {[reps_min_value:reps_max_value]};
      bins min = reps_min_value;
    }

  endgroup : reps_cg

 `DV_FCOV_INSTANTIATE_CG(reps_cg, en_full_cov)

  covergroup reps_cg_1 @(posedge clk_i);

    option.name         = "reps_cg_1";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_reps_ch1: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.reps}{
      bins max_1 = reps_max_value;
      bins mid_1[] = {[reps_min_value:reps_max_value]};
      bins min_1 = reps_min_value;
    }

  endgroup : reps_cg_1

 `DV_FCOV_INSTANTIATE_CG(reps_cg_1, en_full_cov)

  covergroup len_cg @(posedge clk_i);

    option.name         = "len_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_len_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.len}{
      bins maxim = len_max_value;
      bins middle[] = {[len_min_value:len_max_value]};
      bins minim = len_min_value;
    }

  endgroup : len_cg

 `DV_FCOV_INSTANTIATE_CG(len_cg, en_full_cov)

  covergroup len_cg_1 @(posedge clk_i);

    option.name         = "len_cg_1";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    cp_len_ch1: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.len}{
      bins maxim_1 = len_max_value;
      bins middle_1[] = {[len_min_value:len_max_value]};
      bins minim_1 = len_min_value;
    }

  endgroup : len_cg_1

 `DV_FCOV_INSTANTIATE_CG(len_cg_1, en_full_cov)






  covergroup pattgen_op_cg @(posedge clk_i);
    option.name         = "pattgen_op_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;


    cp_pred_top: coverpoint {prediv_q0_match} {
      bins up[]  = {prediv_q0_match};
    }



    walking_1: coverpoint position iff (ch0_data[position]==1
    && $onehot(ch0_data) ) {
      bins b[] = {[0:CH_WIDTH-1]};
    }


    cp_counts_ch0: coverpoint {ones_range(ch0_data, CH_WIDTH)} {
      bins ones[] = {ones_range(ch0_data, CH_WIDTH)};
    }


    cp_count_ones: coverpoint{ch0_data}{
      bins quots = {$countones(ch0_data) == 16};
      bins halfs = {$countones(ch0_data) == 32};
      bins three = {$countones(ch0_data) == 48};
      bins all = {$countones(ch0_data) == 64};
    }

    walking_0: coverpoint position iff (ch0_data[position]==0
    && $onehot(~ch0_data) ) {
      bins b[] = {[0:CH_WIDTH-1]};
    }


    cp_prediv_q0: coverpoint {prediv_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {WIDTH-1};
      bins max = {WIDTH};
      bins mid[1] = {[2:WIDTH -1]};
    }

    cp_clk_cnt_q0: coverpoint {clk_cnt_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {prediv_q0-1};
      bins max = {prediv_q0};
      bins mid[1] = {[2:prediv_q0 -1]};
    }

    cp_reps_q0: coverpoint {reps_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {REP_MAX-1};
      bins max = {REP_MAX};
      bins mid[1] = {[2:REP_MAX -1]};
    }

    cp_rep_cnt_q0: coverpoint {rep_cnt_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {reps_q0-1};
      bins max = {reps_q0};
      bins mid[1] = {[2:reps_q0 -1]};
    }

    cp_len_q0: coverpoint {len_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {LENGTH_MAX-1};
      bins max = {LENGTH_MAX};
      bins mid[1] = {[2:LENGTH_MAX -1]};
    }

    cp_bit_cnt_q0: coverpoint {bit_cnt_q0}{
      bins zero = {0};
      bins one = {1};
      bins pre_max = {len_q0-1};
      bins max = {len_q0};
      bins mid[1] = {[2:len_q0 -1]};
    }

    cp_ch0_all: coverpoint ch0_sig{
      bins all_ch0[] = {ch0_sig};
    }

    cp_ch1_all: coverpoint ch1_sig{
      bins all_ch1[] = {ch1_sig};
    }

    cp_ch01_all: coverpoint ch01_sig{
      bins all_ch01[] = {ch01_sig};
    }

    cp_cross_ch0: cross cp_en_ch0, cp_ch0_all,
    cp_prediv_q0, cp_clk_cnt_q0, walking_1,
    cp_reps_q0, cp_rep_cnt_q0, cp_len_q0, cp_bit_cnt_q0;
    cp_cross_ch1: cross cp_en_ch1, cp_ch1_all;
    cp_cross_ch01: cross cp_en_ch01, cp_ch01_all;

    cp_rst_ni_x_prediv_q0: cross rst_ni, prediv_q0{
      bins zero = binsof(rst_ni) intersect {0} &&
      binsof(prediv_q0) intersect {0};}

    cp_enab0_x_pcl_int_d0: cross enab0, pcl_int_d0{
      bins zero = binsof(enab0) intersect {0} &&
      binsof(pcl_int_d0) intersect {0};}

    cp_ch0_complete_q0: coverpoint {complete_q0} {
      bins complete_q0[] = {0, 1};
    }

    cp_ch1_complete_q1: coverpoint {complete_q1} {
      bins complete_q1[] = {0, 1};
    }
    // Channel 0 coverpoints
    cp_enable: coverpoint {enab1,enab0} {
      bins CH0_ENABLE  = (2'b00 => 2'b01);
      bins CH0_DISABLE = (2'b01 => 2'b00);
      bins CH1_ENABLE  = (2'b00 => 2'b10);
      bins CH1_DISABLE = (2'b10 => 2'b00);
      bins CHX_ENABLE  = (2'b00 => 2'b11);  // CHX: dual channels
      bins CHX_DISABLE = (2'b11 => 2'b00);
      bins CHX_OTHERS  = default;
    }
    // Channel 0 coverpoints
    cp_ch0_perf: coverpoint {ch0_perf} {
      bins LOW_PERF = {'h0};
      bins TYP_PERF = {!'h0};
    }
    cp_ch0_polarity: coverpoint {u_pattgen_core.ch0_ctrl.polarity} {
      bins TX_CLK_FALL = {1'b0};
      bins TX_CLK_RISE = {1'b1};
    }

    // Channel 1 coverpoints
    cp_ch1_perf: coverpoint {ch1_perf} {
      bins LOW_PERF = {'h0};
      bins TYP_PERF = {!'h0};
    }
    cp_ch1_polarity: coverpoint {u_pattgen_core.ch1_ctrl.polarity} {
      bins TX_CLK_FALL = {1'b0};
      bins TX_CLK_RISE = {1'b1};
    }

    // Cross coverpoints
    cr_ch0_complete_q0: cross cp_enable, cp_ch0_complete_q0 {
      bins CH0_OP_ENABLE  = binsof(cp_enable.CH0_ENABLE) &&
      binsof(cp_ch0_complete_q0);
      bins CH0_OP_DISABLE = binsof(cp_enable.CH0_DISABLE) &&
      binsof(cp_ch0_complete_q0);
    }
    cr_ch1_complete_q1: cross cp_enable, cp_ch1_complete_q1 {
      bins CH1_OP_ENABLE  = binsof(cp_enable.CH1_ENABLE);
      bins CH1_OP_DISABLE = binsof(cp_enable.CH1_DISABLE);
    }
    cr_chx_complete_qx: cross cp_enable, cp_ch0_complete_q0,
    cp_ch1_complete_q1{
      bins CHX_OP_ENABLE  = binsof(cp_enable.CHX_ENABLE);
      bins CHX_OP_DISABLE = binsof(cp_enable.CHX_DISABLE);
    }

    // Cross coverpoints
    cr_ch0_op: cross cp_enable, cp_ch0_polarity, cp_ch0_perf {
      bins CH0_OP_ENABLE  = binsof(cp_enable.CH0_ENABLE);
      bins CH0_OP_DISABLE = binsof(cp_enable.CH0_DISABLE);
    }
    cr_ch1_op: cross cp_enable, cp_ch1_polarity, cp_ch1_perf {
      bins CH1_OP_ENABLE  = binsof(cp_enable.CH1_ENABLE);
      bins CH1_OP_DISABLE = binsof(cp_enable.CH1_DISABLE);
    }
    cr_chx_op: cross cp_enable, cp_ch0_polarity, cp_ch0_perf,
    cp_ch1_polarity, cp_ch1_perf {
      bins CHX_OP_ENABLE  = binsof(cp_enable.CHX_ENABLE);
      bins CHX_OP_DISABLE = binsof(cp_enable.CHX_DISABLE);
    }

  endgroup : pattgen_op_cg

  `DV_FCOV_INSTANTIATE_CG(pattgen_op_cg, en_full_cov)

endinterface : pattgen_cov_if
