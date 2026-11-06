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

  // State save/restore interface via register access
  input  logic   [NumAppsLg-1:0] reg_inst_id_i,
  input  logic                   reg_ptr_clr_i,
  input  logic                   reg_rd_en_i,
  output logic    [RegWidth-1:0] reg_rd_data_o,
  input  logic                   reg_wr_en_i,
  input  logic    [RegWidth-1:0] reg_wr_data_i,
  output logic                   reg_overwrite_alert_o,
  output logic     [NumApps-1:0] reg_restored_o,

  output logic [NumApps-1:0][RsCtrWidth-1:0]      reseed_counter_o,
  output logic [NumApps-1:0]                      inst_state_o,
  output logic [NumApps-1:0][GenBitsCtrWidth-1:0] gen_cnt_o,
  output logic [NumApps-1:0]                      gen_flag_o,

  output logic                                    reg_ptr_err_o
);

  localparam int unsigned NumRegTotBits = StateDbNumRegState * RegWidth;
  localparam int unsigned NumRegPadBits = NumRegTotBits - StateWidth;
  localparam bit [StateDbRegPtrWidth-1:0] LastRegState =
      StateDbRegPtrWidth'(StateDbNumRegState - 1);

  // Internal signals
  logic                          write_en;
  logic                          instance_state;
  logic      [NumRegTotBits-1:0] state_reg_readout;
  logic      [NumRegTotBits-1:0] state_reg_restore;
  logic                          reg_access;
  logic [StateDbRegPtrWidth-1:0] reg_ptr_q;
  logic                          reg_ptr_clr;
  logic                          reg_ptr_incr_en;

  // Registers
  logic       [NumApps-1:0] reg_restored_q, reg_restored_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_restored_q <= '0;
    end else begin
      reg_restored_q <= reg_restored_d;
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
  // Regfile readout and restore logic
  //--------------------------------------------

  assign reg_access = reg_rd_en_i || reg_wr_en_i;

  // The word pointer is shared by reads and writes. It advances on every access, wraps around after
  // the last word and is reset when a new access sequence is started.
  assign reg_ptr_clr = !enable_i || reg_ptr_clr_i || (reg_access && (reg_ptr_q == LastRegState));
  assign reg_ptr_incr_en = reg_access && (reg_ptr_q != LastRegState);

  // SEC_CM: STATE_DB.CTR.REDUN
  prim_count #(
    .Width(StateDbRegPtrWidth),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Incr)
  ) u_prim_count_reg_ptr (
    .clk_i,
    .rst_ni,

    .clr_i    (reg_ptr_clr),
    .set_i    (1'b0),
    .set_cnt_i('0),

    .incr_en_i(reg_ptr_incr_en),
    .decr_en_i(1'b0),
    .step_i   (StateDbRegPtrWidth'(1)),
    .commit_i (1'b1),

    .cnt_o             (reg_ptr_q),
    .cnt_after_commit_o(),
    .err_o             (reg_ptr_err_o)
  );

  // Pad the logic representation of the selected state with zeros to the next multiple of 32.
  // An invalid instance id reads as all zeros.
  assign state_reg_readout = (reg_inst_id_i < NumApps) ?
                             {{NumRegPadBits{1'b0}}, state_q[reg_inst_id_i]} : '0;

  assign reg_rd_data_o = state_reg_readout[reg_ptr_q * RegWidth +: RegWidth];

  // Splice the restored word into the selected state.
  always_comb begin
    state_reg_restore = state_reg_readout;
    state_reg_restore[reg_ptr_q * RegWidth +: RegWidth] = reg_wr_data_i;
  end

  // Indicate a restore of the selected instance once the last word is in the state.
  for (genvar i = 0; i < NumApps; i++) begin : gen_reg_restored
    assign reg_restored_d[i] = reg_wr_en_i && (reg_ptr_q == LastRegState) && (reg_inst_id_i == i);
  end
  assign reg_restored_o = reg_restored_q;

  // Flag an internal update of the selected state while an access sequence is in progress.
  assign reg_overwrite_alert_o = write_en && (wr_data_i.inst_id == reg_inst_id_i) &&
                                 ((reg_ptr_q != '0) || reg_access);

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
    end else begin
      if (reg_wr_en_i) begin
        state_d[reg_inst_id_i] = csrng_state_t'(state_reg_restore[StateWidth-1:0]);
      end
      if (write_en && (wr_data_i.inst_id < NumApps)) begin
        state_d[wr_data_i.inst_id] = '{
          gen_adata_vld: wr_data_i.gen_adata_vld,
          gen_flag:      wr_data_i.gen_flag,
          gen_ctr:       wr_data_i.gen_ctr,
          fips:          wr_data_i.fips,
          inst_state:    instance_state,
          gen_adata:     wr_data_i.gen_adata,
          key_v:         wr_data_i.key_v,
          rs_ctr:        wr_data_i.rs_ctr
        };
      end
    end
  end

  // Unused signals
  logic [SeedLen-1:0] unused_wdata_pdata;
  logic [NumRegPadBits-1:0] unused_restore_pad;
  assign unused_wdata_pdata = wr_data_i.pdata;
  assign unused_restore_pad = state_reg_restore[NumRegTotBits-1:StateWidth];

  // Assertions
  // The current architecture assumes the reseed counter fits into a single register
  `ASSERT_INIT(CsrngRsCtrRegFit, RegWidth >= RsCtrWidth)
  // Reads and writes via the register interface are mutually exclusive.
  `ASSERT(CsrngStateDbRegRdWrExclusive_A, !(reg_rd_en_i && reg_wr_en_i))
  // Restore writes only happen while the instance is halted, so they never coincide with an
  // internal update of the same instance.
  `ASSERT(CsrngStateDbRegWrNoInternalUpdate_A,
      reg_wr_en_i |-> !(write_en && (wr_data_i.inst_id == reg_inst_id_i)))

endmodule
