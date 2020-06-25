// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_mock (
  input logic clk_i,
  input logic rst_ni,

  input logic [4:0] rf_rd_addr_a_i,
  input logic [4:0] rf_rd_addr_b_i,

  input logic [4:0]   rf_wr_addr_i,
  input logic [1:0]   rf_wr_en_i,
  input logic [255:0] rf_wr_data_i,
  input logic         rf_wr_data_sel_i,

  input logic       shift_left_i,
  input logic [7:0] shift_amt_i,
  input logic       shift_en_i,

  input logic [1:0] a_qw_sel_i,
  input logic [1:0] b_qw_sel_i,

  input logic [1:0] pre_acc_shift_i,

  input logic [11:0] imm_i,
  input logic        imm_sel_i,

  input logic zero_acc_i,
  input logic mac_en_i,
  input logic mul_en_i,
  input logic acc_shift_out_i,
  input logic add_en_i,
  input logic sub_en_i,
  input logic psuedo_mod_i,

  input logic [255:0] mod_wr_data_i,
  input logic         mod_wr_en_i,

  output logic [255:0] rf_rd_data_a_o,
  output logic [255:0] rf_rd_data_b_o
);

  logic [255:0] rf_rd_data_a;
  logic [255:0] rf_rd_data_b;
  logic [255:0] rf_wr_data_mux;
  logic [255:0] rf_wr_data_mac;
  logic [255:0] rf_wr_data_alu;

  always_comb begin
    rf_wr_data_mux = '0;

    unique case (1'b1)
      mac_en_i:         rf_wr_data_mux = rf_wr_data_mac;
      mul_en_i:         rf_wr_data_mux = rf_wr_data_mac;
      add_en_i:         rf_wr_data_mux = rf_wr_data_alu;
      sub_en_i:         rf_wr_data_mux = rf_wr_data_alu;
      shift_en_i:       rf_wr_data_mux = rf_wr_data_alu;
      rf_wr_data_sel_i: rf_wr_data_mux = rf_wr_data_i;
      default:          rf_wr_data_mux = '0;
    endcase
  end

  otbn_mac otbn_mac_i (
    .clk_i           ( clk_i             ),
    .rst_ni          ( rst_ni            ),

    .a_i         ( rf_rd_data_a      ),
    .b_i         ( rf_rd_data_b      ),

    .a_qw_sel_i      ( a_qw_sel_i        ),
    .b_qw_sel_i      ( b_qw_sel_i        ),

    .pre_acc_shift_i ( pre_acc_shift_i   ),

    .zero_acc_i      ( zero_acc_i        ),
    .mac_en_i        ( mac_en_i          ),
    .mul_en_i        ( mul_en_i          ),
    .acc_shift_out_i ( acc_shift_out_i   ),

    .res_o           ( rf_wr_data_mac    )
  );

  otbn_alu otbn_alu_i (
    .clk_i         ( clk_i          ),
    .rst_ni        ( rst_ni         ),

    .a_i           ( rf_rd_data_a   ),
    .b_i           ( rf_rd_data_b   ),
    .imm_i         ( imm_i          ),

    .shift_left_i  ( shift_left_i   ),
    .shift_amt_i   ( shift_amt_i    ),

    .imm_sel_i     ( imm_sel_i      ),
    .sub_en_i      ( sub_en_i       ),
    .shift_en_i    ( shift_en_i     ),
    .psuedo_mod_i  ( psuedo_mod_i   ),

    .mod_wr_data_i ( mod_wr_data_i  ),
    .mod_wr_en_i   ( mod_wr_en_i    ),

    .res_o         ( rf_wr_data_alu )
  );

  otbn_wide_regfile otbn_wide_regfile_i (
    .clk_i       ( clk_i          ),
    .rst_ni      ( rst_ni         ),

    .rd_addr_a_i ( rf_rd_addr_a_i ),
    .rd_addr_b_i ( rf_rd_addr_b_i ),

    .wr_addr_i   ( rf_wr_addr_i   ),
    .wr_en_i     ( rf_wr_en_i     ),
    .wr_data_i   ( rf_wr_data_mux ),

    .rd_data_a_o ( rf_rd_data_a   ),
    .rd_data_b_o ( rf_rd_data_b   )
  );

  assign rf_rd_data_a_o = rf_rd_data_a;
  assign rf_rd_data_b_o = rf_rd_data_b;
endmodule
