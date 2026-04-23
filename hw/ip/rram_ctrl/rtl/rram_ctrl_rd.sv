// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM control read handler:
// Handles data interface and counts the requested number of bus words per transaction
// Transactions are then issued to rram_ctrl_mp
//

module rram_ctrl_rd import rram_ctrl_pkg::*; (
  input logic clk_i,
  input logic rst_ni,

  // Software Interface
  input  logic                     op_start_i,
  input  logic [CtrlMaxWordsW-1:0] op_num_words_i,
  output logic                     op_done_o,
  input  logic [BusAddrW-1:0]      op_addr_i,
  output rram_ctrl_err_t           op_err_o,
  output logic [BusAddrW-1:0]      op_err_addr_o,
  output logic                     cnt_err_o,
  output logic                     fsm_err_o,

  // Data interface to arbiter
  input  logic                    rd_ctrl_ready_i,
  output logic                    rd_ctrl_valid_o,
  output logic [BusFullWidth-1:0] rd_ctrl_data_o,

  // Read interface to rram_ctrl_mp
  output logic                    rram_req_o,
  output logic [BusAddrW-1:0]     rram_addr_o,
  output logic                    rram_ovfl_o,
  input  logic [BusFullWidth-1:0] rram_data_i,
  input  logic                    rram_done_i,
  input  logic                    rram_rd_err_i,
  input  logic                    rram_mp_err_i
);

  // Encoding generated at commit 0d4f05ad06 using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 8913483484 --distance 4 --states 3 --bits 6
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 4
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    StIdle = 6'b111001,
    StNorm = 6'b101110,
    StErr  = 6'b010111
  } state_e;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  logic [CtrlMaxWordsW-1:0] cnt;
  logic                     cnt_hit;
  logic [BusAddrW:0]        int_addr;
  logic                     rd_done, rd_wr;
  logic                     err_sel; // 1 selects error data, 0 selects normal data

  rram_ctrl_err_t op_err_q, op_err_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_err_q <= '0;
    end else if (op_start_i && op_done_o) begin
      op_err_q <= '0;
    end else begin
      op_err_q <= op_err_d;
    end
  end

  prim_count #(
    .Width(CtrlMaxWordsW),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (op_start_i && op_done_o),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (rd_wr),
    .decr_en_i         (1'b0),
    .step_i            (CtrlMaxWordsW'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (cnt),
    .cnt_after_commit_o(),
    .err_o             (cnt_err_o)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_err_addr_o <= '0;
    end else if ((op_err_q == 0) && (op_err_d != 0)) begin
      op_err_addr_o <= rram_addr_o;
    end
  end

  assign rd_done = rram_req_o & rram_done_i;
  assign cnt_hit = (cnt >= op_num_words_i);

  // when error'd, continue to complete existing read transaction but fill in with all 1's
  // if this is not done, software may continue to attempt to read out of the fifo
  // and eventually cause a bus deadlock as the fifo would be empty
  // This scheme is similar to burst completion up an error
  always_comb begin
    state_d    = state_q;
    rram_req_o = 1'b0;
    rd_wr      = 1'b0;
    op_done_o  = 1'b0;
    op_err_d   = op_err_q;
    fsm_err_o  = 1'b0;

    unique case (state_q)
      StIdle: begin
        if (cnt_err_o) begin
          // if counter error is encountered, just go to error state
          state_d = StErr;
        end else if (op_start_i) begin
          state_d = |op_err_d ? StErr : StNorm;
        end
      end

      // Note the address counter is incremented on rd_done
      // and cleared when the entire operation is complete.
      StNorm: begin
        rram_req_o = op_start_i & rd_ctrl_ready_i;

        if (rd_done) begin
          op_err_d.mp_err = rram_mp_err_i;
          op_err_d.rd_err = rram_rd_err_i;

          rd_wr = 1'b1;

          if (cnt_hit) begin
            op_done_o = 1'b1;
            state_d   = StIdle;
          end else begin
            state_d = |op_err_d ? StErr : StNorm;
          end
        end
      end

      StErr: begin
        rd_wr = rd_ctrl_ready_i;

        if (rd_ctrl_ready_i && cnt_hit) begin
          state_d   = StIdle;
          op_done_o = 1'b1;
        end
      end
      default: fsm_err_o = 1'b1;
    endcase
  end

  // overflow error detection is not here, but instead handled at memory protection
  assign int_addr    = op_addr_i + BusAddrW'(cnt);
  assign rram_addr_o = int_addr[BusAddrW-1:0];
  assign rram_ovfl_o = int_addr[BusAddrW];
  // if error, return "empty" data
  assign err_sel = rd_wr & |op_err_o;

  // When there is no error, return the rram data and remove the addr-xor
  // When there is an error, return invalid data with the correct bus integrity
  logic [BusWidth-1:0] addr_xor;
  logic [BusWidth-1:0] data_xor;
  logic [BusFullWidth-1:0] inv_data_integ;
  tlul_data_integ_enc u_bus_intg (
    .data_i     ({BusWidth{1'b1}}),
    .data_intg_o(inv_data_integ)
  );

  assign addr_xor = {{(BusWidth-BusAddrW){1'b0}}, int_addr[BusAddrW-1:0]};
  assign data_xor = rram_data_i[BusWidth-1:0] ^ addr_xor;

  assign rd_ctrl_data_o = err_sel ? inv_data_integ :
                                    {rram_data_i[BusFullWidth-1:BusWidth], data_xor};

  assign rd_ctrl_valid_o = rd_wr;

  assign op_err_o = op_err_q | op_err_d;

endmodule // rram_ctrl_rd
