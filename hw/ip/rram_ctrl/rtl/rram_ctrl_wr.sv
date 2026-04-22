// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM ctrl write handler:
// Handles fifo interface and counts the requested number of bus words per transaction
// Transactions are then issued to rram_ctrl_mp
//

module rram_ctrl_wr import rram_ctrl_pkg::*; (
  input logic clk_i,
  input logic rst_ni,

  // Control interface
  input  logic                     op_start_i,
  input  logic [CtrlMaxWordsW-1:0] op_num_words_i,
  output logic                     op_done_o,
  input  logic [BusAddrW-1:0]      op_addr_i,
  output rram_ctrl_err_t           op_err_o,
  output logic [BusAddrW-1:0]      op_err_addr_o,
  output logic                     cnt_err_o,
  output logic                     fsm_err_o,

  // FIFO interface
  input  logic                    fifo_rvalid_i,
  input  logic [BusFullWidth-1:0] fifo_rdata_i,
  output logic                    fifo_rready_o,

  // Write interface to rram_ctrl_mp
  output logic                    rram_req_o,
  output logic [BusAddrW-1:0]     rram_addr_o,
  output logic                    rram_ovfl_o,
  output logic [BusFullWidth-1:0] rram_data_o,
  output logic                    rram_last_o, // last beat of a write
  input  logic                    rram_done_i,
  input  logic                    rram_mp_err_i,
  input  logic                    rram_wr_intg_err_i
);

  // Encoding generated at commit 61d4d1cd9e using Python 3.10.19 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 718361455 --distance 4 --states 2 --bits 5
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 3
  //
  localparam int StateWidth = 5;
  typedef enum logic [StateWidth-1:0] {
    StNorm = 5'b11001,
    StErr  = 5'b00010
  } state_e;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StNorm)

  logic [CtrlMaxWordsW-1:0] cnt;
  logic                     cnt_hit;
  logic [BusAddrW:0]        int_addr;
  logic                     wr_done;

  rram_ctrl_err_t op_err_q, op_err_d;

  prim_count #(
    .Width(CtrlMaxWordsW)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (op_start_i && op_done_o),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (fifo_rready_o),
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
      op_err_addr_o <= int_addr[BusAddrW-1:0];
    end
  end

  assign wr_done = rram_req_o && rram_done_i;
  assign cnt_hit = (cnt >= op_num_words_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_err_q <= '0;
    end else if (op_start_i && op_done_o) begin
      op_err_q <= '0;
    end else begin
      op_err_q <= op_err_d;
    end
  end

  // When an error occured, abort write operation and empty write fifo
  always_comb begin
    state_d       = state_q;
    rram_req_o    = 1'b0;
    fifo_rready_o = 1'b0;
    op_done_o     = 1'b0;
    op_err_d      = op_err_q;
    fsm_err_o     = 1'b0;

    unique case (state_q)

      // Note the address counter is incremented on wr_done
      // and cleared when the entire operation is complete.
      StNorm: begin

        if (cnt_err_o) begin
          // if count error'd don't bother doing anything else, just try to finish
          state_d = StErr;

        end else if (op_start_i) begin
          rram_req_o = fifo_rvalid_i;

          if (wr_done) begin
            op_err_d.mp_err = rram_mp_err_i;
            op_err_d.wr_err = rram_wr_intg_err_i;
            fifo_rready_o   = 1'b1;

            if (cnt_hit) begin
              op_done_o = 1'b1;
            end else begin
              state_d = |op_err_d ? StErr : StNorm;
            end
          end

        end
      end
      StErr: begin
        fifo_rready_o = fifo_rvalid_i;

        if (fifo_rvalid_i && cnt_hit) begin
          state_d   = StNorm;
          op_done_o = 1'b1;
        end
      end
      default: fsm_err_o = 1'b1;
    endcase
  end

  assign rram_data_o = fifo_rdata_i;
  assign int_addr    = op_addr_i + BusAddrW'(cnt);
  assign rram_addr_o = int_addr[BusAddrW-1:0];
  assign rram_ovfl_o = int_addr[BusAddrW];
  assign rram_last_o = rram_req_o & cnt_hit;
  assign op_err_o    = op_err_q | op_err_d;

endmodule // rram_ctrl_wr
