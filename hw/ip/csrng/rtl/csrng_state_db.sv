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
(
  input  logic                       clk_i,
  input  logic                       rst_ni,

  // Global enable
  input  logic                       enable_i,

  // Read interface for the core data path
  input  logic       [NumAppsLg-1:0] rd_inst_id_i,
  output csrng_state_db_t            rd_state_o,

  // Write interface (from ctr_drbg)
  input  logic                       wr_vld_i,
  input  csrng_core_data_t           wr_data_i,

  // Context import/export interface.
  input  logic [NumAppsLg-1:0]       reg_inst_id_i,

  input  logic                       reg_ptr_incr_i,
  input  logic                       reg_ptr_clr_i,

  output logic [CmdBusWidth-1:0]     reg_rd_val_o,
  input  logic                       reg_wr_vld_i,
  input  logic [CmdBusWidth-1:0]     reg_wr_data_i,

  // Update path for instantiated state in command stage.
  output logic                       wr_inst_state_o,
  output logic                       wr_inst_state_vld_o,

  output logic [NumApps-1:0][RsCtrWidth-1:0] reseed_counter_o,

  output logic reg_rd_ptr_err_o
);

  localparam int unsigned NumRegStateLg = $clog2(StateDbNumWords);
  localparam bit [NumRegStateLg-1:0] LastRegState = NumRegStateLg'(StateDbNumWords - 1);

  // Internal signals
  logic                         write_en;
  logic                         instance_state;
  logic [StateDbStateWidth-1:0] state_reg_readout;
  logic [StateDbStateWidth-1:0] state_reg_write_merged;
  logic                         write_merged_state_db_vld;
  csrng_state_db_t              write_merged_state_db;

  // Registers
  logic [NumRegStateLg-1:0] reg_rd_ptr_q;

  // State storage, no reset required
  csrng_state_db_t [NumApps-1:0] state_q, state_d;

  always_ff @(posedge clk_i) begin
    state_q <= state_d;
  end

  // State readout for core data path
  assign rd_state_o = (rd_inst_id_i < NumApps) ? state_q[rd_inst_id_i] : '0;

  //--------------------------------------------
  // Regfile readout/write logic
  //--------------------------------------------

  logic reg_rd_ptr_incr_en, reg_ptr_clr;
  assign reg_rd_ptr_incr_en = reg_ptr_incr_i && (reg_rd_ptr_q != LastRegState);
  assign reg_ptr_clr = !enable_i || reg_ptr_clr_i ||
                       (reg_ptr_incr_i && (reg_rd_ptr_q == LastRegState));

  // SEC_CM: STATE_DB.CTR.REDUN
  prim_count #(
    .Width(NumRegStateLg),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Incr)
  ) u_prim_count_reg_rd_ptr (
    .clk_i,
    .rst_ni,

    .clr_i    (reg_ptr_clr),
    .set_i    (1'b0),
    .set_cnt_i('0),

    .incr_en_i(reg_rd_ptr_incr_en),
    .decr_en_i(1'b0),
    .step_i   (NumRegStateLg'(1)),
    .commit_i (1'b1),

    .cnt_o             (reg_rd_ptr_q),
    .cnt_after_commit_o(),
    .err_o             (reg_rd_ptr_err_o)
  );

  // Check if reg_inst_id_i points at one of the existing apps.
  assign state_reg_readout = (reg_inst_id_i < NumApps) ? state_q[reg_inst_id_i] : '0;

  // Check if the state_db word pointer is in range.
  logic reg_rd_ptr_in_range;
  assign reg_rd_ptr_in_range = reg_rd_ptr_q < NumRegStateLg'(StateDbNumWords);
  assign reg_rd_val_o = reg_rd_ptr_in_range ?
      state_reg_readout[reg_rd_ptr_q * CmdBusWidth +: CmdBusWidth] : '0;

  // Splice the newly imported word into the state DB.
  always_comb begin
    state_reg_write_merged = state_reg_readout;
    if (reg_rd_ptr_in_range) begin
      state_reg_write_merged[reg_rd_ptr_q * CmdBusWidth +: CmdBusWidth] = reg_wr_data_i;
    end
  end

  // Import data and valid signals.
  assign write_merged_state_db_vld = reg_wr_vld_i && (reg_inst_id_i < NumApps);
  assign write_merged_state_db = csrng_state_db_t'(state_reg_write_merged);

  // Forward the instantiated state data and valid signal to the command stage.
  assign wr_inst_state_o       = write_merged_state_db.inst_state;
  assign wr_inst_state_vld_o   = write_merged_state_db_vld &&
                                 (reg_rd_ptr_q == NumRegStateLg'(InstStateRegIdx));

  // The reseed counters are always readable via register interface.
  for (genvar i = 0; i < NumApps; i++) begin : gen_reseed_counter
    assign reseed_counter_o[i] = state_q[i].rs_ctr;
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
      // ctr_drbg write.
      if (write_en && (wr_data_i.inst_id < NumApps)) begin
        state_d[wr_data_i.inst_id] = '{
          rsvd:       '0,
          fips:       wr_data_i.fips,
          key:        wr_data_i.key,
          v:          wr_data_i.v,
          rs_ctr:     wr_data_i.rs_ctr,
          inst_state: instance_state
        };
      end
      // Import data interface write.
      if (write_merged_state_db_vld) begin
        state_d[reg_inst_id_i] = write_merged_state_db;
      end
    end
  end

  // Unused signals
  logic [SeedLen-1:0] unused_wdata_pdata;
  assign unused_wdata_pdata = wr_data_i.pdata;

  // Assertions
  // The current architecture assumes the reseed counter fits into a single register
  `ASSERT_INIT(CsrngRsCtrRegFit, CmdBusWidth >= RsCtrWidth)
  // An internal-state IMPORT command may never coincide with a normal ctr_drbg write-back
  // for the same instance.
  `ASSERT(CsrngStateDbNoConcurrentWrites_A,
      !(write_en && write_merged_state_db_vld && (wr_data_i.inst_id == reg_inst_id_i)))

endmodule
