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
  flash_ctrl_err_t         op_err_o,
  input [BusAddrW-1:0]     op_addr_i,
  input                    op_addr_oob_i,
  output logic [BusAddrW-1:0] op_err_addr_o,
  output logic             cnt_err_o,

  // FIFO Interface
  input                    data_rdy_i,
  output logic [BusFullWidth-1:0] data_o,
  output logic             data_wr_o,

  // Flash Macro Interface
  output logic             flash_req_o,
  output logic [BusAddrW-1:0] flash_addr_o,
  output logic             flash_ovfl_o,
  input [BusFullWidth-1:0] flash_data_i,
  input                    flash_done_i,
  input                    flash_rd_err_i,
  input                    flash_mp_err_i
);

  typedef enum logic [1:0] {
    StIdle,
    StNorm,
    StErr
  } state_e;

  state_e st_q, st_d;
  logic [11:0] cnt;
  logic cnt_hit;
  logic [BusAddrW:0] int_addr;
  logic txn_done;
  logic err_sel; //1 selects error data, 0 selects normal data
  flash_ctrl_err_t op_err_q, op_err_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st_q <= StIdle;
    end else begin
      st_q <= st_d;
    end
  end

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
    .Width(12)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(op_start_i && op_done_o),
    .set_i('0),
    .set_cnt_i('0),
    .incr_en_i(data_wr_o),
    .decr_en_i(1'b0),
    .step_i(12'h1),
    .cnt_o(cnt),
    .cnt_next_o(),
    .err_o(cnt_err_o)
  );

  //always_ff @(posedge clk_i or negedge rst_ni) begin
  //  if (!rst_ni) begin
  //    cnt <= '0;
  //  end else if (op_start_i && op_done_o) begin
  //    cnt <= '0;
  //  end else if (data_wr_o) begin
  //    cnt <= cnt + 1'b1;
  //  end
  //end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_err_addr_o <= '0;
    end else if (~|op_err_q && |op_err_d) begin
      op_err_addr_o <= flash_addr_o;
    end
  end

  assign txn_done = flash_req_o & flash_done_i;
  assign cnt_hit = (cnt >= op_num_words_i);


  // when error'd, continue to complete existing read transaction but fill in with all 1's
  // if this is not done, software may continue to attempt to read out of the fifo
  // and eventually cause a bus deadlock as the fifo would be empty
  // This scheme is similar to burst completion up an error
  always_comb begin
    st_d = st_q;
    flash_req_o = 1'b0;
    data_wr_o = 1'b0;
    op_done_o = 1'b0;
    op_err_d = op_err_q;

    unique case (st_q)
      StIdle: begin
        if (cnt_err_o) begin
          // if counter error is encountered, just go to error state
          st_d = StErr;
        end else if (op_start_i) begin
          op_err_d.oob_err = op_addr_oob_i;
          st_d = |op_err_d ? StErr : StNorm;
        end
      end

      // Note the address counter is incremented on tx_done
      // and cleared when the entire operation is complete.
      StNorm: begin
        flash_req_o = op_start_i & data_rdy_i;

        if (txn_done) begin
          op_err_d.mp_err = flash_mp_err_i;
          op_err_d.rd_err = flash_rd_err_i;

          data_wr_o = 1'b1;

          if (cnt_hit) begin
            op_done_o = 1'b1;
            st_d = StIdle;
          end else begin
            st_d = |op_err_d ? StErr : StNorm;
          end
        end
      end

      StErr: begin
        data_wr_o = data_rdy_i;

        if (data_rdy_i && cnt_hit) begin
          st_d = StIdle;
          op_done_o = 1'b1;
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
  assign err_sel = data_wr_o & |op_err_o;

  // When there is no error, return flash data directly.
  // When the error is a read error specifically, also return flash data as the integrity is
  // natively handled by the phy.
  // All other errors do not result in an actual transaction to the flash, and therefore must use
  // the locally available error value.
  assign data_o = ~err_sel | (err_sel & op_err_o.rd_err) ? flash_data_i :
                  prim_secded_pkg::prim_secded_inv_39_32_enc({BusWidth{1'b1}});
  assign op_err_o = op_err_q | op_err_d;


endmodule // flash_ctrl_rd
