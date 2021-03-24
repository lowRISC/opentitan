// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Read Control
//

module flash_ctrl_rd import flash_ctrl_pkg::*; (
  input clk_i,
  input rst_ni,

  // Software Interface
  input                    op_start_i,
  input  [11:0]            op_num_words_i,
  output logic             op_done_o,
  output logic             op_err_o,
  input [BusAddrW-1:0]     op_addr_i,

  // FIFO Interface
  input                    data_rdy_i,
  output logic [BusWidth-1:0] data_o,
  output logic             data_wr_o,

  // Flash Macro Interface
  output logic             flash_req_o,
  output logic [BusAddrW-1:0] flash_addr_o,
  output logic             flash_ovfl_o,
  input [BusWidth-1:0]     flash_data_i,
  input                    flash_done_i,
  input                    flash_error_i
);

  typedef enum logic {
    StNorm  = 'h0,
    StErr   = 'h1
  } state_e;

  state_e st, st_nxt;
  logic [11:0] cnt, cnt_nxt;
  logic cnt_hit;
  logic [BusAddrW:0] int_addr;
  logic txn_done;
  logic err_sel; //1 selects error data, 0 selects normal data

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
      st <= StNorm;
    end else begin
      cnt <= cnt_nxt;
      st <= st_nxt;
    end
  end

  assign txn_done = flash_req_o & flash_done_i;
  assign cnt_hit = (cnt == op_num_words_i);

  // when error'd, continue to complete existing read transaction but fill in with all 1's
  // if this is not done, software may continue to attempt to read out of the fifo
  // and eventually cause a bus deadlock as the fifo would be empty
  // This scheme is similar to burst completion up an error
  always_comb begin
    st_nxt = st;
    cnt_nxt = cnt;
    flash_req_o = 1'b0;
    data_wr_o = 1'b0;
    op_done_o = 1'b0;
    op_err_o = 1'b0;
    err_sel = 1'b0;

    unique case (st)
      StNorm: begin
        flash_req_o = op_start_i & data_rdy_i;

        if (txn_done && cnt_hit) begin
          cnt_nxt = '0;
          data_wr_o = 1'b1;
          op_done_o = 1'b1;
          op_err_o = flash_error_i;
        end else if (txn_done) begin
          cnt_nxt = cnt + 1'b1;
          data_wr_o = 1'b1;
          err_sel = flash_error_i;
          st_nxt = flash_error_i ? StErr : StNorm;
        end
      end
      StErr: begin
        data_wr_o = data_rdy_i;
        err_sel = 1'b1;

        if (data_rdy_i && cnt_hit) begin
          st_nxt = StNorm;
          cnt_nxt = '0;
          op_done_o = 1'b1;
          op_err_o = 1'b1;
        end else if (data_rdy_i) begin
          cnt_nxt = cnt + 1'b1;
        end
      end
      default:;
    endcase // unique case (st)
  end

  // overflow error detection is not here, but instead handled at memory protection
  assign int_addr = op_addr_i + BusAddrW'(cnt);
  assign flash_addr_o = int_addr[0 +: BusAddrW];
  assign flash_ovfl_o = int_addr[BusAddrW];
  // if error, return "empty" data
  assign data_o = err_sel ? {BusWidth{1'b1}} : flash_data_i;


endmodule // flash_ctrl_rd
