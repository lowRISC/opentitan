// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for PATTGEN.
interface pattgen_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  bit ch0_perf, ch1_perf;
  assign ch0_perf = {u_pattgen_core.ch0_ctrl.len, 
                     u_pattgen_core.ch0_ctrl.reps, 
                     u_pattgen_core.ch0_ctrl.prediv} == 'h0;
  assign ch1_perf = {u_pattgen_core.ch1_ctrl.len,
                     u_pattgen_core.ch1_ctrl.reps,
                     u_pattgen_core.ch1_ctrl.prediv} == 'h0;

  covergroup pattgen_op_cg @(u_pattgen_core.ch0_ctrl.enable or u_pattgen_core.ch1_ctrl.enable);
    option.name         = "pattgen_op_cg";
    option.comment      = "PATTGEN CH0 and CH1 operation";
    option.per_instance = 1;

    // Channel 0 coverpoints
    cp_enable: coverpoint {u_pattgen_core.ch1_ctrl.enable, u_pattgen_core.ch0_ctrl.enable} {
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
    cr_ch0_op: cross cp_enable, cp_ch0_polarity, cp_ch0_perf {
      bins CH0_OP_ENABLE  = binsof(cp_enable.CH0_ENABLE);
      bins CH0_OP_DISABLE = binsof(cp_enable.CH0_DISABLE);
    }
    cr_ch1_op: cross cp_enable, cp_ch1_polarity, cp_ch1_perf {
      bins CH1_OP_ENABLE  = binsof(cp_enable.CH1_ENABLE);
      bins CH1_OP_DISABLE = binsof(cp_enable.CH1_DISABLE);
    }
    cr_chx_op: cross cp_enable, cp_ch0_polarity, cp_ch0_perf, cp_ch1_polarity, cp_ch1_perf {
      bins CHX_OP_ENABLE  = binsof(cp_enable.CHX_ENABLE);
      bins CHX_OP_DISABLE = binsof(cp_enable.CHX_DISABLE);
    }

  endgroup : pattgen_op_cg

  `DV_FCOV_INSTANTIATE_CG(pattgen_op_cg, en_full_cov)

endinterface : pattgen_cov_if
