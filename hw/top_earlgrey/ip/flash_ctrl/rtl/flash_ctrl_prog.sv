// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Prog Control
//

module flash_ctrl_prog import flash_ctrl_pkg::*; (
  input clk_i,
  input rst_ni,

  // Control Interface
  input                    op_start_i,
  input  [11:0]            op_num_words_i,
  output logic             op_done_o,
  output logic             op_err_o,
  input [BusAddrW-1:0]     op_addr_i,
  input flash_prog_e       op_type_i,
  input [ProgTypes-1:0]    type_avail_i,

  // FIFO Interface
  input                    data_rdy_i,
  input  [BusWidth-1:0]    data_i,
  output logic             data_rd_o,

  // Flash Macro Interface
  output logic             flash_req_o,
  output logic [BusAddrW-1:0] flash_addr_o,
  output logic             flash_ovfl_o,
  output logic [BusWidth-1:0] flash_data_o,
  output logic             flash_last_o, // last beat of prog data
  output flash_prog_e      flash_type_o,
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


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
      st <= StNorm;
    end else begin
      cnt <= cnt_nxt;
      st <= st_nxt;
    end
  end

  assign txn_done = flash_req_o && flash_done_i;
  assign cnt_hit = (cnt == op_num_words_i);

  // if the requested prog type is available
  logic prog_type_avail;
  assign prog_type_avail = type_avail_i[op_type_i];

  // program resolution check
  // if the incoming beat is larger than the maximum program resolution, error
  // immediately and do not allow it to start.
  localparam int WindowWidth = BusAddrW - BusPgmResWidth;
  logic [WindowWidth-1:0] start_window, end_window;
  logic [BusAddrW-1:0] end_addr;
  logic win_err;
  assign end_addr = op_addr_i + BusAddrW'(op_num_words_i);
  assign start_window = op_addr_i[BusAddrW-1:BusPgmResWidth];
  assign end_window = end_addr[BusAddrW-1:BusPgmResWidth];
  assign win_err = start_window != end_window;

  // when error'd, continue to drain all program fifo contents like normal operation
  // if this is not done, software may fill up the fifo without anyone
  // draining the contents, leading to a lockup
  always_comb begin
    st_nxt = st;
    cnt_nxt = cnt;
    flash_req_o = 1'b0;
    data_rd_o = 1'b0;
    op_done_o = 1'b0;
    op_err_o = 1'b0;

    unique case (st)
      StNorm: begin
        // if the select operation type is not available, error
        if (op_start_i && prog_type_avail && !win_err) begin
          flash_req_o = data_rdy_i;

          if(txn_done && cnt_hit) begin
            cnt_nxt = '0;
            data_rd_o = 1'b1;
            op_done_o = 1'b1;
            op_err_o = flash_error_i;
          end else if(txn_done) begin
            cnt_nxt = cnt + 1'b1;
            data_rd_o = 1'b1;
            st_nxt = flash_error_i ? StErr : StNorm;
          end
        end else if (op_start_i && (!prog_type_avail || win_err)) begin
          st_nxt = StErr;
        end
      end
      StErr: begin
        data_rd_o = data_rdy_i;

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

  assign flash_data_o = data_i;
  assign int_addr = op_addr_i + BusAddrW'(cnt);
  assign flash_addr_o = int_addr[0 +: BusAddrW];
  assign flash_ovfl_o = int_addr[BusAddrW];
  assign flash_last_o = flash_req_o & cnt_hit;
  assign flash_type_o = op_type_i;

  // unused signals
  logic [BusPgmResWidth-1:0] unused_end_addr;
  assign unused_end_addr = end_addr[BusPgmResWidth-1:0];

endmodule // flash_ctrl_prog
