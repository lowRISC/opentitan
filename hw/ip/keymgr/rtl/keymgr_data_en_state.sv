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

  input adv_en_i,
  input id_en_i,
  input gen_en_i,
  input op_done_i,
  input op_start_i,
  output logic data_en_o,
  output logic fsm_err_o
);

  // This is a separate data path from the FSM used to control the data_en_o output
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (50.00%)
  //  6: |||||||||||||||| (40.00%)
  //  7: |||| (10.00%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 5
  // Maximum Hamming weight: 7
  //
  localparam int DataStateWidth = 10;
  typedef enum logic [DataStateWidth-1:0] {
    StCtrlDataIdle    = 10'b1001110111,
    StCtrlDataEn      = 10'b1110001011,
    StCtrlDataDis     = 10'b0110100110,
    StCtrlDataWait    = 10'b1010111000,
    StCtrlDataInvalid = 10'b1111010100
  } state_e;

  state_e state_d, state_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [DataStateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  // SEC_CM: DATA.FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(state_e),
    .Width(DataStateWidth),
    .ResetValue(DataStateWidth'(StCtrlDataIdle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d     ),
    .state_o ( state_raw_q )
  );

  // The below control path is used for modulating the datapath to sideload and sw keys.
  // This path is separate from the data_valid_o path, thus creating two separate attack points.
  // The data is only enabled when a non-advance operation is invoked.
  // When an advance operation is called, the data is disabled. It will stay disabled until an
  // entire completion sequence is seen (op_done_o assert -> start_i de-assertion).
  // When a generate operation is called, the data is enabled.  However, any indication of this
  // supposedly being an advance call will force the path to disable again.
  always_comb begin
    state_d = state_q;
    data_en_o = 1'b0;
    fsm_err_o = 1'b0;
    unique case (state_q)

      StCtrlDataIdle: begin
        if (adv_en_i) begin
          state_d = StCtrlDataDis;
        end else if (id_en_i || gen_en_i) begin
          state_d = StCtrlDataEn;
        end
      end

      StCtrlDataEn: begin
        data_en_o = 1'b1;
        if (op_done_i) begin
          state_d = StCtrlDataWait;
        end else if (adv_en_i) begin
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
