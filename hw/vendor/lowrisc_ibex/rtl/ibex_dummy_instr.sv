// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Dummy instruction module
 *
 * Provides pseudo-randomly inserted fake instructions for secure code obfuscation
 */

// SEC_CM: CTRL_FLOW.UNPREDICTABLE
module ibex_dummy_instr import ibex_pkg::*; #(
    parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault
) (
  // Clock and reset
  input  logic        clk_i,
  input  logic        rst_ni,

  // Interface to CSRs
  input  logic        dummy_instr_en_i,
  input  logic [2:0]  dummy_instr_mask_i,
  input  logic        dummy_instr_seed_en_i,
  input  logic [31:0] dummy_instr_seed_i,

  // Interface to IF stage
  input  logic        fetch_valid_i,
  input  logic        id_in_ready_i,
  output logic        insert_dummy_instr_o,
  output logic [31:0] dummy_instr_data_o
);

  localparam int unsigned TIMEOUT_CNT_W = 5;
  localparam int unsigned OP_W          = 5;

  typedef enum logic [1:0] {
    DUMMY_ADD = 2'b00,
    DUMMY_MUL = 2'b01,
    DUMMY_DIV = 2'b10,
    DUMMY_AND = 2'b11
  } dummy_instr_e;

  typedef struct packed {
    dummy_instr_e             instr_type;
    logic [OP_W-1:0]          op_b;
    logic [OP_W-1:0]          op_a;
    logic [TIMEOUT_CNT_W-1:0] cnt;
  } lfsr_data_t;
  localparam int unsigned LFSR_OUT_W = $bits(lfsr_data_t);

  lfsr_data_t               lfsr_data;
  logic [TIMEOUT_CNT_W-1:0] dummy_cnt_incr, dummy_cnt_threshold;
  logic [TIMEOUT_CNT_W-1:0] dummy_cnt_d, dummy_cnt_q;
  logic                     dummy_cnt_en;
  logic                     lfsr_en;
  logic [LFSR_OUT_W-1:0]    lfsr_state;
  logic                     insert_dummy_instr;
  logic [6:0]               dummy_set;
  logic [2:0]               dummy_opcode;
  logic [31:0]              dummy_instr;
  logic [31:0]              dummy_instr_seed_q, dummy_instr_seed_d;

  // Shift the LFSR every time we insert an instruction
  assign lfsr_en = insert_dummy_instr & id_in_ready_i;

  assign dummy_instr_seed_d = dummy_instr_seed_q ^ dummy_instr_seed_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dummy_instr_seed_q <= '0;
    end else if (dummy_instr_seed_en_i) begin
      dummy_instr_seed_q <= dummy_instr_seed_d;
    end
  end

  prim_lfsr #(
      .LfsrDw      ( LfsrWidth       ),
      .StateOutDw  ( LFSR_OUT_W      ),
      .DefaultSeed ( RndCnstLfsrSeed ),
      .StatePermEn ( 1'b1            ),
      .StatePerm   ( RndCnstLfsrPerm )
  ) lfsr_i (
      .clk_i     ( clk_i                 ),
      .rst_ni    ( rst_ni                ),
      .seed_en_i ( dummy_instr_seed_en_i ),
      .seed_i    ( dummy_instr_seed_d    ),
      .lfsr_en_i ( lfsr_en               ),
      .entropy_i ( '0                    ),
      .state_o   ( lfsr_state            )
  );

  // Extract fields from LFSR
  assign lfsr_data = lfsr_data_t'(lfsr_state);

  // Set count threshold for inserting a new instruction. This is the pseudo-random value from the
  // LFSR with a mask applied (based on CSR config data) to shorten the period if required.
  assign dummy_cnt_threshold = lfsr_data.cnt & {dummy_instr_mask_i,{TIMEOUT_CNT_W-3{1'b1}}};
  assign dummy_cnt_incr      = dummy_cnt_q + {{TIMEOUT_CNT_W-1{1'b0}},1'b1};
  // Clear the counter everytime a new instruction is inserted
  assign dummy_cnt_d         = insert_dummy_instr ? '0 : dummy_cnt_incr;
  // Increment the counter for each executed instruction while dummy instuctions are
  // enabled.
  assign dummy_cnt_en        = dummy_instr_en_i & id_in_ready_i &
                               (fetch_valid_i | insert_dummy_instr);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dummy_cnt_q <= '0;
    end else if (dummy_cnt_en) begin
      dummy_cnt_q <= dummy_cnt_d;
    end
  end

  // Insert a dummy instruction each time the counter hits the threshold
  assign insert_dummy_instr = dummy_instr_en_i & (dummy_cnt_q == dummy_cnt_threshold);

  // Encode instruction
  always_comb begin
    unique case (lfsr_data.instr_type)
      DUMMY_ADD: begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b000;
      end
      DUMMY_MUL: begin
        dummy_set    = 7'b0000001;
        dummy_opcode = 3'b000;
      end
      DUMMY_DIV: begin
        dummy_set    = 7'b0000001;
        dummy_opcode = 3'b100;
      end
      DUMMY_AND: begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b111;
      end
      default: begin
        dummy_set    = 7'b0000000;
        dummy_opcode = 3'b000;
      end
    endcase
  end

  //                    SET        RS2             RS1             OP            RD
  assign dummy_instr = {dummy_set, lfsr_data.op_b, lfsr_data.op_a, dummy_opcode, 5'h00, 7'h33};

  // Assign outputs
  assign insert_dummy_instr_o = insert_dummy_instr;
  assign dummy_instr_data_o   = dummy_instr;

endmodule
