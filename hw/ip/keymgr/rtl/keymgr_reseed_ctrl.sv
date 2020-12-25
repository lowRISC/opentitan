// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager entropy reseed controls
//

`include "prim_assert.sv"

module keymgr_reseed_ctrl import keymgr_pkg::*; (
  input clk_i,
  input rst_ni,
  input clk_edn_i,
  input rst_edn_ni,

  // interface to keymgr_ctrl
  input reseed_req_i,
  output logic reseed_ack_o,

  // interface to software
  input [15:0] reseed_interval_i,

  // interface to edn
  output edn_pkg::edn_req_t edn_o,
  input edn_pkg::edn_rsp_t edn_i,

  // interface to lfsr
  output logic seed_en_o,
  output logic [LfsrWidth-1:0] seed_o
);

  localparam int EdnRounds = LfsrWidth / EdnWidth;
  localparam int EdnCntWidth = prim_util_pkg::vbits(EdnRounds);

  // counter to track number of edn rounds
  logic [EdnCntWidth-1:0] edn_cnt;
  logic edn_txn_done;
  logic edn_done;
  logic edn_req, edn_ack;
  logic [EdnWidth-1:0] edn_data;

  // This tracks how many edn rounds are required to fill up
  // one required entry.
  assign edn_txn_done = edn_req & edn_ack;
  assign edn_done = (edn_cnt == EdnRounds - 1) & edn_txn_done;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      edn_cnt <= '0;
    end else if (edn_done) begin
      edn_cnt <= '0;
    end else if (edn_txn_done) begin
      edn_cnt <= edn_cnt - 1'b1;
    end
  end

  // first activation of edn counter
  logic first_use;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      first_use <= 1'b1;
    end else if (edn_done) begin
      first_use <= 1'b0;
    end
  end

  // whenever reseed count drops to 0, issue a request and wait for ack
  logic [15:0] reseed_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reseed_cnt <= '{default: 1};
    end else if(edn_done) begin
      reseed_cnt <= reseed_interval_i;
    end else if(reseed_req_i) begin
      reseed_cnt <= '0;
    end else if(|reseed_cnt && !first_use) begin
      reseed_cnt <= reseed_cnt - 1'b1;
    end
  end

  assign edn_req = (reseed_cnt == '0);
  assign reseed_ack_o = reseed_req_i & edn_done;
  assign seed_en_o = edn_done;

  if (EdnRounds == 1) begin : gen_same_width
    assign seed_o = edn_data;
  end else begin : gen_mult_width
    // hold one less transaction in storage
    localparam int DeltaWidth = LfsrWidth-EdnWidth;
    logic [DeltaWidth-1:0] seed_q;

    if (DeltaWidth > EdnWidth) begin : gen_greater_width
      always_ff @(posedge clk_i) begin
        if (edn_txn_done) begin
          seed_q <= {seed_q[0 +: DeltaWidth-EdnWidth], edn_data};
        end
      end
    end else begin : gen_double_width
      always_ff @(posedge clk_i) begin
        if (edn_txn_done) begin
          seed_q <= edn_data;
        end
      end
    end

    assign seed_o = {seed_q, edn_data};
  end

  //req/ack interface to edn
  prim_sync_reqack u_reqack (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i(clk_edn_i),
    .rst_dst_ni(rst_edn_ni),
    .src_req_i(edn_req),
    .src_ack_o(edn_ack),
    .dst_req_o(edn_o.edn_req),
    .dst_ack_i(edn_i.edn_ack)
  );

  // capture the data on edn domain since the ack interface
  // finishes before the source domain is able to see it
  always_ff @(posedge clk_edn_i) begin
    if (edn_o.edn_req && edn_i.edn_ack) begin
      edn_data <= edn_i.edn_bus;
    end
  end


  logic unused_fips;
  assign unused_fips = edn_i.edn_fips;

endmodule // keymgr_reseed_ctrl
