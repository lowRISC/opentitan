// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng state data base module
//
// This is the container for accessing the current
//    working state for a given drbg instance.

`include "prim_assert.sv"

module csrng_state_db
  import csrng_pkg::*;
  import csrng_reg_pkg::NumApps;
#(
  localparam int unsigned RegWidth = top_pkg::TL_DW
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,

  // Global enable
  input  logic                   enable_i,

  // Read interface for the core data path
  input  logic   [NumAppsLg-1:0] rd_inst_id_i,
  output csrng_state_t           rd_state_o,

  // Write interface
  input  logic                   wr_vld_i,
  input  csrng_core_data_t       wr_data_i,

  // State dump interface via register access
  input  logic                   reg_rd_en_i,
  input  logic     [NumApps-1:0] reg_rd_regfile_en_i,

  input  logic                   reg_rd_id_vld_i,
  input  logic [InstIdWidth-1:0] reg_rd_id_i,
  input  logic                   reg_rd_strb_i,
  output logic    [RegWidth-1:0] reg_rd_val_o,

  output logic [NumApps-1:0][RsCtrWidth-1:0]      reseed_counter_o,
  output logic [NumApps-1:0]                      inst_state_o,
  output logic [NumApps-1:0][GenBitsCtrWidth-1:0] gen_cnt_o,
  output logic [NumApps-1:0]                      gen_flag_o,

  output logic                                    reg_ptr_err_o
);

  // Only the fields up to and including fips are readable via the register interface.
  localparam int unsigned RegStateWidth = RsCtrWidth + BlkLen + KeyLen + 2;

  // Number of registers per state with synthesis-friendly $ceil(RegStateWidth / RegWidth)
  localparam int unsigned            NumRegState   = (RegStateWidth + RegWidth - 1) / RegWidth;
  localparam int unsigned            NumRegStateLg = $clog2(NumRegState);
  localparam int unsigned            NumRegTotBits = NumRegState * RegWidth;
  localparam int unsigned            NumRegPadBits = NumRegTotBits - RegStateWidth;
  localparam bit [NumRegStateLg-1:0] LastRegState  = NumRegStateLg'(NumRegState - 1);

  // Internal signals
  logic                     write_en;
  logic                     instance_state;
  logic [NumRegTotBits-1:0] state_reg_readout;
  logic [NumRegStateLg-1:0] reg_rd_ptr_q;
  logic                     reg_rd_last;
  logic                     reg_rd_ptr_clr;
  logic                     reg_rd_ptr_incr_en;

  // Registers
  logic     [NumAppsLg-1:0] reg_rd_id_q, reg_rd_id_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_rd_id_q  <= '0;
    end else begin
      reg_rd_id_q  <= reg_rd_id_d;
    end
  end

  // State storage, no reset required
  csrng_state_t [NumApps-1:0] state_q, state_d;

  always_ff @(posedge clk_i) begin
    state_q <= state_d;
  end

  // State readout for core data path
  assign rd_state_o = (rd_inst_id_i < NumApps) ? state_q[rd_inst_id_i] : '0;

  //--------------------------------------------
  // Regfile readout logic
  //--------------------------------------------

  always_comb begin
    reg_rd_id_d = reg_rd_id_q;
    if (!enable_i) begin
      reg_rd_id_d = '0;
    end else if (reg_rd_id_vld_i) begin
      reg_rd_id_d = reg_rd_id_i[NumAppsLg-1:0];
    end
  end

  // The last word of the selected state is being read.
  assign reg_rd_last = reg_rd_strb_i && (reg_rd_ptr_q == LastRegState);

  // Reset the regfile read pointer when a new instance is selected for readout. The pointer wraps
  // around after the last word.
  assign reg_rd_ptr_clr = !enable_i || !reg_rd_en_i || reg_rd_id_vld_i || reg_rd_last;
  assign reg_rd_ptr_incr_en = reg_rd_strb_i && !reg_rd_last;

  // SEC_CM: STATE_DB.CTR.REDUN
  prim_count #(
    .Width(NumRegStateLg),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Incr)
  ) u_prim_count_reg_ptr (
    .clk_i,
    .rst_ni,

    .clr_i    (reg_rd_ptr_clr),
    .set_i    (1'b0),
    .set_cnt_i('0),

    .incr_en_i(reg_rd_ptr_incr_en),
    .decr_en_i(1'b0),
    .step_i   (NumRegStateLg'(1)),
    .commit_i (1'b1),

    .cnt_o             (reg_rd_ptr_q),
    .cnt_after_commit_o(),
    .err_o             (reg_ptr_err_o)
  );

  // Pad the logic representation of the selected state with zeros to the next multiple of 32
  assign state_reg_readout = (reg_rd_id_q < NumApps) ?
                             {{NumRegPadBits{1'b0}}, state_q[reg_rd_id_q][RegStateWidth-1:0]} :
                             '0;

  always_comb begin
    reg_rd_val_o = '0;
    if (reg_rd_en_i && (reg_rd_id_q < NumApps ? reg_rd_regfile_en_i[reg_rd_id_q] : 1'b0) &&
        (reg_rd_ptr_q < NumRegState)) begin
      reg_rd_val_o = state_reg_readout[reg_rd_ptr_q * RegWidth +: RegWidth];
    end
  end

  // The reseed counters are always readable via register interface. The instantiated and generate
  // command state is used by the command stages.
  for (genvar i = 0; i < NumApps; i++) begin : gen_reseed_counter
    assign reseed_counter_o[i] = state_q[i].rs_ctr;
    assign inst_state_o[i]     = state_q[i].inst_state;
    assign gen_cnt_o[i]        = state_q[i].gen_ctr;
    assign gen_flag_o[i]       = state_q[i].gen_flag;
  end

  //--------------------------------------------
  // Write logic
  //--------------------------------------------

  // All valid commands except UNInstatiate set the instance state as 'instantiated'.
  assign instance_state = (wr_data_i.cmd == INS) || (wr_data_i.cmd == RES) ||
                          (wr_data_i.cmd == GEN) || (wr_data_i.cmd == UPD);

  assign write_en = enable_i && wr_vld_i;

  always_comb begin
    state_d = state_q;

    if (!enable_i) begin
      state_d = '0;
    end else if (write_en && (wr_data_i.inst_id < NumApps)) begin
      state_d[wr_data_i.inst_id] = '{
        gen_adata_vld: wr_data_i.gen_adata_vld,
        gen_adata:     wr_data_i.gen_adata,
        gen_flag:      wr_data_i.gen_flag,
        gen_ctr:       wr_data_i.gen_ctr,
        fips:          wr_data_i.fips,
        key_v:         wr_data_i.key_v,
        rs_ctr:        wr_data_i.rs_ctr,
        inst_state:    instance_state
      };
    end
  end

  // Unused signals
  logic [SeedLen-1:0] unused_wdata_pdata;
  logic [InstIdWidth-NumAppsLg-1:0] unused_reg_rd_id;
  assign unused_wdata_pdata = wr_data_i.pdata;
  assign unused_reg_rd_id = reg_rd_id_i[InstIdWidth-1:NumAppsLg];

  // Assertions
  // The current architecture assumes the reseed counter fits into a single register
  `ASSERT_INIT(CsrngRsCtrRegFit, RegWidth >= RsCtrWidth)

endmodule
