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
  input  logic                   reg_rd_otp_en_i,
  input  logic     [NumApps-1:0] reg_rd_regfile_en_i,

  input  logic                   reg_rd_id_vld_i,
  input  logic [InstIdWidth-1:0] reg_rd_id_i,
  input  logic                   reg_rd_strb_i,
  output logic    [RegWidth-1:0] reg_rd_val_o,

  output logic [NumApps-1:0][RsCtrWidth-1:0] reseed_counter_o
);

  // Number of registers per state with synthesis-friendly $ceil(StateWidth / RegWidth)
  localparam int unsigned NumRegState   = (StateWidth + RegWidth - 1) / RegWidth;
  localparam int unsigned NumRegStateLg = $clog2(NumRegState);
  localparam int unsigned NumRegTotBits = NumRegState * RegWidth;
  localparam int unsigned NumRegPadBits = NumRegTotBits - StateWidth;

  // Internal signals
  logic                     write_en;
  logic                     instance_state;
  logic [NumRegTotBits-1:0] state_reg_readout;

  // Registers
  logic [NumRegStateLg-1:0] reg_rd_ptr_q, reg_rd_ptr_d;
  logic     [NumAppsLg-1:0] reg_rd_id_q, reg_rd_id_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_rd_ptr_q <= '0;
      reg_rd_id_q  <= '0;
    end else begin
      reg_rd_ptr_q <= reg_rd_ptr_d;
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

  // Reset the regfile read pointer when a new instance is selected for readout
  always_comb begin
    reg_rd_ptr_d = reg_rd_ptr_q;
    if (!enable_i || !reg_rd_otp_en_i) begin
      reg_rd_ptr_d = '1;
    end else if (reg_rd_id_vld_i || (reg_rd_ptr_q == NumRegState)) begin
      reg_rd_ptr_d = '0;
    end else if (reg_rd_strb_i) begin
      reg_rd_ptr_d = reg_rd_ptr_q + 1;
    end
  end

  // Pad the logic representation of the selected state with zeros to the next multiple of 32
  assign state_reg_readout = {{NumRegPadBits{1'b0}}, state_q[reg_rd_id_q]};

  always_comb begin
    reg_rd_val_o = '0;
    if (reg_rd_otp_en_i && reg_rd_regfile_en_i[reg_rd_id_q] &&
        (reg_rd_ptr_q < NumRegState)) begin
      reg_rd_val_o = state_reg_readout[reg_rd_ptr_q * RegWidth +: RegWidth];
    end
  end

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
    end else if (write_en && (wr_data_i.inst_id < NumApps)) begin
      state_d[wr_data_i.inst_id] = '{
        fips:       wr_data_i.fips,
        key:        wr_data_i.key,
        v:          wr_data_i.v,
        rs_ctr:     wr_data_i.rs_ctr,
        inst_state: instance_state
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
