// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager date enable generation
// This is a redundant alternative to data_valid

`include "prim_assert.sv"

module keymgr_data_en_state
  import keymgr_pkg::*;
  import keymgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input prim_mubi_pkg::mubi4_t hw_sel_i,
  input adv_en_i,
  input id_en_i,
  input gen_en_i,
  input op_done_i,
  input op_start_i,
  output logic data_hw_en_o,
  output logic data_sw_en_o,
  output logic fsm_err_o
);

  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_test_false_strict;
  import prim_mubi_pkg::mubi4_test_false_loose;

  // This is a separate data path from the FSM used to control the data_en outputs
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 6 -n 10 \
  //      -s 2015444891 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||| (33.33%)
  //  6: |||||||||||||||||||| (40.00%)
  //  7: ||||||||||||| (26.67%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  localparam int DataStateWidth = 10;
  typedef enum logic [DataStateWidth-1:0] {
    StCtrlDataIdle    = 10'b1000010000,
    StCtrlDataHwEn    = 10'b0001100100,
    StCtrlDataSwEn    = 10'b1110101110,
    StCtrlDataDis     = 10'b0010011111,
    StCtrlDataWait    = 10'b0111110011,
    StCtrlDataInvalid = 10'b1111001001
  } state_e;

  state_e state_d, state_q;

  // SEC_CM: DATA.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StCtrlDataIdle)

  // The below control path is used for modulating the datapath to sideload and sw keys.
  // This path is separate from the data_valid_o path, thus creating two separate attack points.
  // The data is only enabled when a non-advance operation is invoked.
  // When an advance operation is called, the data is disabled. It will stay disabled until an
  // entire completion sequence is seen (op_done_o assert -> start_i de-assertion).
  // When a generate operation is called, the data is enabled.  However, any indication of this
  // supposedly being an advance call will force the path to disable again.
  always_comb begin
    state_d = state_q;
    fsm_err_o = 1'b0;
    data_hw_en_o = 1'b0;
    data_sw_en_o = 1'b0;
    unique case (state_q)

      StCtrlDataIdle: begin
        if (adv_en_i) begin
          state_d = StCtrlDataDis;
        end else if ((id_en_i || gen_en_i) && mubi4_test_true_strict(hw_sel_i)) begin
          state_d = StCtrlDataHwEn;
        end else if ((id_en_i || gen_en_i) && mubi4_test_false_strict(hw_sel_i)) begin
          state_d = StCtrlDataSwEn;
        end else if (id_en_i || gen_en_i) begin
          state_d = StCtrlDataDis;
        end
      end

      StCtrlDataHwEn: begin
        data_hw_en_o = 1'b1;
        if (op_done_i) begin
          state_d = StCtrlDataWait;
        end else if (adv_en_i || mubi4_test_false_loose(hw_sel_i)) begin
          state_d = StCtrlDataDis;
        end
      end

      StCtrlDataSwEn: begin
        data_sw_en_o = 1'b1;
        if (op_done_i) begin
          state_d = StCtrlDataWait;
        end else if (adv_en_i || mubi4_test_true_loose(hw_sel_i)) begin
          state_d = StCtrlDataDis;
        end
      end

      StCtrlDataDis: begin
        if (op_done_i) begin
          state_d = StCtrlDataWait;
        end
      end

      StCtrlDataWait: begin
        if (!op_start_i) begin
          state_d = StCtrlDataIdle;
        end
      end

      default: begin
        fsm_err_o = 1'b1;
      end


    endcase // unique case (state_q)
  end


endmodule // keymgr_data_en_state
