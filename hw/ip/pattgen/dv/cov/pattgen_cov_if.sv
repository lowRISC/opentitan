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

  uint data_max = 32'hffffffff;
  uint data_min = 32'hfffffffb;
  uint data_max_low = 20;
  uint data_min_low = 0;
  uint prediv_max_value = 32'hffffffff;
  uint prediv_min_value = 32'hfffffffc;
  uint reps_max_value = 10'h3ff;
  uint reps_min_value = 10'h3fc;
  uint len_max_value = 10'h3f;
  uint len_min_value = 10'h3c;

  bit rep_cnt_en_ch0 = `CH0_PATH.rep_cnt_en;
  bit complete_q1 = `CH1_PATH.complete_q;
  bit len_q0 = `CH0_PATH.len_q;
  bit pcl_int_d0 = `CH0_PATH.pcl_int_d;
  bit reps_q0 = `CH0_PATH.reps_q;
  bit clk_cnt_q0 = `CH0_PATH.clk_cnt_q;
  bit bit_cnt_q0 = `CH0_PATH.bit_cnt_q;
  bit rep_cnt_q0 = `CH0_PATH.rep_cnt_q;
  bit clk_cnt_q1 = `CH1_PATH.clk_cnt_q;
  bit prediv_q0 = `CH0_PATH.prediv_q;
  bit prediv_q1 = `CH1_PATH.prediv_q;


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

    wire ch0_cnt_match_prediv = (`CH0_PATH.prediv_q == `CH0_PATH.clk_cnt_q);
    wire ch0_cnt_reset = (`CH0_PATH.clk_cnt_q == 0);
    wire ch0_cnt_match_len = (`CH0_PATH.len_q == u_pattgen_core.chan0.bit_cnt_q);
    wire ch0_cnt_len_reset = (`CH0_PATH.bit_cnt_q == 0);
    wire ch0_cnt_match_reps = (`CH0_PATH.reps_q == u_pattgen_core.chan0.rep_cnt_q);
    wire ch0_cnt_reset_reps = (`CH0_PATH.rep_cnt_q == 0);

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

    bit data_match = (tb.dut.u_pattgen_core.ch0_ctrl.data[31:0] == data_max);

  //NOTE upper and lower parts of data cannot be accessed with CHAN* macro
  //because channels receive merged 64 bit data.

  covergroup data_00_cg @(posedge clk_i);

    option.name         = "data_00_cg";
    option.comment      = "Data coverage in LSB Chan0";

    cp_data_ch0: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[31:0]}{
      bins maxim = {data_max};
      bins mid[] = {[data_min + 1:data_max - 1]};
      bins minim = {data_min};
    }

  endgroup : data_00_cg

 `DV_FCOV_INSTANTIATE_CG(data_00_cg, en_full_cov)

  covergroup data_01_cg @(posedge clk_i);

    option.name         = "data_01_cg";
    option.comment      = "Data coverage in MSB Chan0";

    cp_data_ch1: coverpoint {tb.dut.u_pattgen_core.ch0_ctrl.data[63:32]}{
      bins maxim = {data_max};
      bins mid[] = {[data_min +1:data_max - 1]};
      bins minim = {data_min};
    }

  endgroup : data_01_cg

 `DV_FCOV_INSTANTIATE_CG(data_01_cg, en_full_cov)

  covergroup data_10_cg @(posedge clk_i);

    option.name         = "data_10_cg";
    option.comment      = "Data coverage in LSB Chan1";

    cp_data_ch10: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[31:0]}{
      bins maxim = {data_max};
      bins mid[] = {[data_min +1 : data_max - 1]};
      bins minim = {data_min};
    }

  endgroup : data_10_cg

 `DV_FCOV_INSTANTIATE_CG(data_10_cg, en_full_cov)

  covergroup data_11_cg @(posedge clk_i);

    option.name         = "data_11_cg";
    option.comment      = "Data coverage in MSB Chan1";

    cp_data_ch1: coverpoint {tb.dut.u_pattgen_core.ch1_ctrl.data[63:32]}{
      bins maxim = {data_max};
      bins mid[] = {[data_min + 1:data_max - 1]};
      bins minim = {data_min};
    }

  endgroup : data_11_cg

 `DV_FCOV_INSTANTIATE_CG(data_11_cg, en_full_cov)

  covergroup prediv_cg @(posedge clk_i);

    option.name         = "prediv_cg";
    option.comment      = "Chan0 Pre-divide clock coefficient coverage";

    cp_prediv_ch0: coverpoint {`CH0_PATH.prediv_q}{
      bins maxim = {prediv_max_value};
      bins mid[] = {[prediv_min_value + 1:prediv_max_value - 1]};
      bins minim = {prediv_min_value};
    }

  endgroup : prediv_cg

 `DV_FCOV_INSTANTIATE_CG(prediv_cg, en_full_cov)

  covergroup prediv_1_cg @(posedge clk_i);

    option.name         = "prediv_1_cg";
    option.comment      = "Chan1 Pre-divide clock coefficient coverage";

    cp_prediv_ch1: coverpoint {`CH1_PATH.prediv_q}{
      bins maxim = {prediv_max_value};
      bins mid[] = {[prediv_min_value + 1:prediv_max_value - 1]};
      bins minim = {prediv_min_value};
    }

  endgroup : prediv_1_cg

 `DV_FCOV_INSTANTIATE_CG(prediv_1_cg, en_full_cov)

  covergroup reps_cg @(posedge clk_i);

    option.name         = "reps_cg";
    option.comment      = "Chan0 repetition coefficient coverage";

    cp_reps_ch0: coverpoint {`CH0_PATH.reps_q}{
      bins maxim = {reps_max_value};
      bins mid[] = {[reps_min_value + 1:reps_max_value - 1]};
      bins minim = {reps_min_value};
    }

  endgroup : reps_cg

 `DV_FCOV_INSTANTIATE_CG(reps_cg, en_full_cov)

  covergroup reps_cg_1 @(posedge clk_i);

    option.name         = "reps_cg_1";
    option.comment      = "Chan1 repetition coefficient coverage";

    cp_reps_ch1: coverpoint {`CH1_PATH.reps_q}{
      bins maxim_1 = {reps_max_value};
      bins mid_1[] = {[reps_min_value + 1:reps_max_value - 1]};
      bins minim_1 = {reps_min_value};

    }

  endgroup : reps_cg_1

 `DV_FCOV_INSTANTIATE_CG(reps_cg_1, en_full_cov)

  covergroup len_cg @(posedge clk_i);

    option.name         = "len_cg";
    option.comment      = "Chan0 length coverage";

    cp_len_ch0: coverpoint {`CH0_PATH.len_q}{
      bins maxim = {len_max_value};
      bins middle[] = {[len_min_value + 1:len_max_value - 1]};
      bins minim = {len_min_value};
    }

  endgroup : len_cg

 `DV_FCOV_INSTANTIATE_CG(len_cg, en_full_cov)

  covergroup len_cg_1 @(posedge clk_i);

    option.name         = "len_cg_1";
    option.comment      = "Chan1 length coverage";

    cp_len_ch1: coverpoint {`CH1_PATH.len_q}{
      bins maxim_1 = {len_max_value};
      bins middle_1[] = {[len_min_value + 1:len_max_value - 1]};
      bins minim_1 = {len_min_value};

    }

  endgroup : len_cg_1

 `DV_FCOV_INSTANTIATE_CG(len_cg_1, en_full_cov)

  covergroup pattgen_op_cg @(posedge clk_i);
    option.name         = "pattgen_op_cg";
    option.comment      = "Chan0 and Chan1 interrupt done and event done coverage";

    cp_intr_done_ch0_o: coverpoint u_pattgen_core.intr_done_ch0_o;
    cp_intr_done_ch1_o: coverpoint u_pattgen_core.intr_done_ch1_o;
    cp_event_done_ch0: coverpoint  u_pattgen_core.chan0.event_done_o;
    cp_event_done_ch1: coverpoint  u_pattgen_core.chan1.event_done_o;

  endgroup : pattgen_op_cg

  `DV_FCOV_INSTANTIATE_CG(pattgen_op_cg, en_full_cov)

endinterface : pattgen_cov_if
