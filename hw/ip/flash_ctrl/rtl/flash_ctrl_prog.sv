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
  output flash_ctrl_err_t  op_err_o,
  input [BusAddrW-1:0]     op_addr_i,
  input                    op_addr_oob_i,
  input flash_prog_e       op_type_i,
  input [ProgTypes-1:0]    type_avail_i,
  output logic [BusAddrW-1:0] op_err_addr_o,
  output logic             cnt_err_o,

  // FIFO Interface
  input                    data_rdy_i,
  input  [BusFullWidth-1:0] data_i,
  output logic             data_rd_o,

  // Flash Macro Interface
  output logic             flash_req_o,
  output logic [BusAddrW-1:0] flash_addr_o,
  output logic             flash_ovfl_o,
  output logic [BusFullWidth-1:0] flash_data_o,
  output logic             flash_last_o, // last beat of prog data
  output flash_prog_e      flash_type_o,
  input                    flash_done_i,
  input                    flash_mp_err_i,
  input                    flash_prog_intg_err_i
);

  typedef enum logic {
    StNorm  = 'h0,
    StErr   = 'h1
  } state_e;

  state_e st_q, st_d;
  logic [11:0] cnt;
  logic cnt_hit;
  logic [BusAddrW:0] int_addr;
  logic txn_done;

  flash_ctrl_err_t op_err_q, op_err_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st_q <= StNorm;
    end else begin
      st_q <= st_d;
    end
  end

  //always_ff @(posedge clk_i or negedge rst_ni) begin
  //  if (!rst_ni) begin
  //    cnt <= '0;
  //  end else if (op_start_i && op_done_o) begin
  //    cnt <= '0;
  //  end else if (data_rd_o) begin
  //    cnt <= cnt + 1'b1;
  //  end
  //end

  prim_count #(
    .Width(12)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(op_start_i && op_done_o),
    .set_i('0),
    .set_cnt_i('0),
    .incr_en_i(data_rd_o),
    .decr_en_i(1'b0),
    .step_i(12'h1),
    .cnt_o(cnt),
    .cnt_next_o(),
    .err_o(cnt_err_o)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_err_addr_o <= '0;
    end else if (~|op_err_q && |op_err_d) begin
      op_err_addr_o <= flash_addr_o;
    end
  end

  assign txn_done = flash_req_o && flash_done_i;
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

  // if the requested prog type is available
  logic prog_type_avail;
  assign prog_type_avail = type_avail_i[op_type_i];

  // program resolution check
  // if the incoming beat is larger than the maximum program resolution, error
  // immediately and do not allow it to start.
  localparam int WindowWidth = BusAddrW - BusPgmResWidth;
  logic [WindowWidth-1:0] start_window, end_window;
  logic [BusAddrW-1:0] end_addr;
  logic pgm_res_err;
  logic win_err;
  assign end_addr = op_addr_i + BusAddrW'(op_num_words_i);
  assign start_window = op_addr_i[BusAddrW-1:BusPgmResWidth];
  assign end_window = end_addr[BusAddrW-1:BusPgmResWidth];
  assign pgm_res_err = start_window != end_window;
  assign win_err = pgm_res_err | op_addr_oob_i;

  // when error'd, continue to drain all program fifo contents like normal operation
  // if this is not done, software may fill up the fifo without anyone
  // draining the contents, leading to a lockup
  always_comb begin
    st_d = st_q;
    flash_req_o = 1'b0;
    data_rd_o = 1'b0;
    op_done_o = 1'b0;
    op_err_d = op_err_q;

    unique case (st_q)

      // Note the address counter is incremented on tx_done
      // and cleared when the entire operation is complete.
      StNorm: begin

        if (cnt_err_o) begin
          // if count error'd don't bother doing anything else, just try to finish
          st_d = StErr;

        end else if (op_start_i && prog_type_avail && !win_err) begin
          // if the select operation type is not available, error
          flash_req_o = data_rdy_i;

          if (txn_done) begin
            op_err_d.mp_err = flash_mp_err_i;
            op_err_d.prog_err = flash_prog_intg_err_i;
            data_rd_o = 1'b1;

            if (cnt_hit) begin
              op_done_o = 1'b1;
            end else begin
              st_d = |op_err_d ? StErr : StNorm;
            end
          end

        end else if (op_start_i && (!prog_type_avail || win_err)) begin
          op_err_d.oob_err = op_addr_oob_i;
          op_err_d.prog_type_err = !prog_type_avail;
          op_err_d.prog_win_err = pgm_res_err;
          st_d = StErr;
        end
      end
      StErr: begin
        data_rd_o = data_rdy_i;

        if (data_rdy_i && cnt_hit) begin
          st_d = StNorm;
          op_done_o = 1'b1;
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
  assign op_err_o = op_err_q | op_err_d;

  // unused signals
  logic [BusPgmResWidth-1:0] unused_end_addr;
  assign unused_end_addr = end_addr[BusPgmResWidth-1:0];

endmodule // flash_ctrl_prog
