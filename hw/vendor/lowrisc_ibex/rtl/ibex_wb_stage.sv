// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Writeback Stage
 *
 * Writeback is an optional third pipeline stage. It writes data back to the register file that was
 * produced in the ID/EX stage or awaits a response to a load/store (LSU writes direct to register
 * file for load data). If the writeback stage is not present (WritebackStage == 0) this acts as
 * a simple passthrough to write data direct to the register file.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module ibex_wb_stage #(
  parameter bit ResetAll          = 1'b0,
  parameter bit WritebackStage    = 1'b0,
  parameter bit DummyInstructions = 1'b0
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     en_wb_i,
  input  ibex_pkg::wb_instr_type_e instr_type_wb_i,
  input  logic [31:0]              pc_id_i,
  input  logic                     instr_is_compressed_id_i,
  input  logic                     instr_perf_count_id_i,

  output logic                     ready_wb_o,
  output logic                     rf_write_wb_o,
  output logic                     outstanding_load_wb_o,
  output logic                     outstanding_store_wb_o,
  output logic [31:0]              pc_wb_o,
  output logic                     perf_instr_ret_wb_o,
  output logic                     perf_instr_ret_compressed_wb_o,
  output logic                     perf_instr_ret_wb_spec_o,
  output logic                     perf_instr_ret_compressed_wb_spec_o,

  input  logic [4:0]               rf_waddr_id_i,
  input  logic [31:0]              rf_wdata_id_i,
  input  logic                     rf_we_id_i,

  input  logic                     dummy_instr_id_i,

  input  logic [31:0]              rf_wdata_lsu_i,
  input  logic                     rf_we_lsu_i,

  output logic [31:0]              rf_wdata_fwd_wb_o,

  output logic [4:0]               rf_waddr_wb_o,
  output logic [31:0]              rf_wdata_wb_o,
  output logic                     rf_we_wb_o,

  output logic                     dummy_instr_wb_o,

  input logic                      lsu_resp_valid_i,
  input logic                      lsu_resp_err_i,

  output logic                     instr_done_wb_o
);

  import ibex_pkg::*;

  // 0 == RF write from ID
  // 1 == RF write from LSU
  logic [31:0] rf_wdata_wb_mux    [2];
  logic [1:0]  rf_wdata_wb_mux_we;

  if (WritebackStage) begin : g_writeback_stage
    logic [31:0]    rf_wdata_wb_q;
    logic           rf_we_wb_q;
    logic [4:0]     rf_waddr_wb_q;

    logic           wb_done;

    logic           wb_valid_q;
    logic [31:0]    wb_pc_q;
    logic           wb_compressed_q;
    logic           wb_count_q;
    wb_instr_type_e wb_instr_type_q;

    logic           wb_valid_d;

    // Stage becomes valid if an instruction enters for ID/EX and valid is cleared when instruction
    // is done
    assign wb_valid_d = (en_wb_i & ready_wb_o) | (wb_valid_q & ~wb_done);

    // Writeback for non load/store instructions always completes in a cycle (so instantly done)
    // Writeback for load/store must wait for response to be received by the LSU
    // Signal only relevant if wb_valid_q set
    assign wb_done = (wb_instr_type_q == WB_INSTR_OTHER) | lsu_resp_valid_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wb_valid_q <= 1'b0;
      end else begin
        wb_valid_q <= wb_valid_d;
      end
    end

    if (ResetAll) begin : g_wb_regs_ra
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_we_wb_q      <= '0;
          rf_waddr_wb_q   <= '0;
          rf_wdata_wb_q   <= '0;
          wb_instr_type_q <= wb_instr_type_e'(0);
          wb_pc_q         <= '0;
          wb_compressed_q <= '0;
          wb_count_q      <= '0;
        end else if (en_wb_i) begin
          rf_we_wb_q      <= rf_we_id_i;
          rf_waddr_wb_q   <= rf_waddr_id_i;
          rf_wdata_wb_q   <= rf_wdata_id_i;
          wb_instr_type_q <= instr_type_wb_i;
          wb_pc_q         <= pc_id_i;
          wb_compressed_q <= instr_is_compressed_id_i;
          wb_count_q      <= instr_perf_count_id_i;
        end
      end
    end else begin : g_wb_regs_nr
      always_ff @(posedge clk_i) begin
        if (en_wb_i) begin
          rf_we_wb_q      <= rf_we_id_i;
          rf_waddr_wb_q   <= rf_waddr_id_i;
          rf_wdata_wb_q   <= rf_wdata_id_i;
          wb_instr_type_q <= instr_type_wb_i;
          wb_pc_q         <= pc_id_i;
          wb_compressed_q <= instr_is_compressed_id_i;
          wb_count_q      <= instr_perf_count_id_i;
        end
      end
    end

    assign rf_waddr_wb_o         = rf_waddr_wb_q;
    assign rf_wdata_wb_mux[0]    = rf_wdata_wb_q;
    assign rf_wdata_wb_mux_we[0] = rf_we_wb_q & wb_valid_q;

    assign ready_wb_o = ~wb_valid_q | wb_done;

    // Instruction in writeback will be writing to register file if either rf_we is set or writeback
    // is awaiting load data. This is used for determining RF read hazards in ID/EX
    assign rf_write_wb_o = wb_valid_q & (rf_we_wb_q | (wb_instr_type_q == WB_INSTR_LOAD));

    assign outstanding_load_wb_o  = wb_valid_q & (wb_instr_type_q == WB_INSTR_LOAD);
    assign outstanding_store_wb_o = wb_valid_q & (wb_instr_type_q == WB_INSTR_STORE);

    assign pc_wb_o = wb_pc_q;

    assign instr_done_wb_o = wb_valid_q & wb_done;

    // Increment instruction retire counters for valid instructions which are not lsu errors.
    // Speculative versions of the signals do not factor in exceptions and whether the instruction
    // is done yet. These are used to get correct values for instructions reading the relevant
    // performance counters in the ID stage.
    assign perf_instr_ret_wb_spec_o            = wb_count_q;
    assign perf_instr_ret_compressed_wb_spec_o = perf_instr_ret_wb_spec_o & wb_compressed_q;
    assign perf_instr_ret_wb_o                 = instr_done_wb_o & wb_count_q &
                                                 ~(lsu_resp_valid_i & lsu_resp_err_i);
    assign perf_instr_ret_compressed_wb_o      = perf_instr_ret_wb_o & wb_compressed_q;

    // Forward data that will be written to the RF back to ID to resolve data hazards. The flopped
    // rf_wdata_wb_q is used rather than rf_wdata_wb_o as the latter includes read data from memory
    // that returns too late to be used on the forwarding path.
    assign rf_wdata_fwd_wb_o = rf_wdata_wb_q;

    // For FI hardening, only forward LSU write enable if we're actually waiting for it.
    assign rf_wdata_wb_mux_we[1] = outstanding_load_wb_o & rf_we_lsu_i;

    if (DummyInstructions) begin : g_dummy_instr_wb
      logic dummy_instr_wb_q;

      if (ResetAll) begin : g_dummy_instr_wb_regs_ra
        always_ff @(posedge clk_i or negedge rst_ni) begin
          if (!rst_ni) begin
            dummy_instr_wb_q <= 1'b0;
          end else if (en_wb_i) begin
            dummy_instr_wb_q <= dummy_instr_id_i;
          end
        end
      end else begin : g_dummy_instr_wb_regs_nr
        always_ff @(posedge clk_i) begin
          if (en_wb_i) begin
            dummy_instr_wb_q <= dummy_instr_id_i;
          end
        end
      end

      assign dummy_instr_wb_o = dummy_instr_wb_q;
    end else begin : g_no_dummy_instr_wb
      logic  unused_dummy_instr_id;
      assign unused_dummy_instr_id = dummy_instr_id_i;

      assign dummy_instr_wb_o = 1'b0;
    end
  end else begin : g_bypass_wb
    // without writeback stage just pass through register write signals
    assign rf_waddr_wb_o         = rf_waddr_id_i;
    assign rf_wdata_wb_mux[0]    = rf_wdata_id_i;
    assign rf_wdata_wb_mux_we[0] = rf_we_id_i;
    assign rf_wdata_wb_mux_we[1] = rf_we_lsu_i;

    assign dummy_instr_wb_o = dummy_instr_id_i;

    // Increment instruction retire counters for valid instructions which are not lsu errors.
    // The speculative signals are always 0 when no writeback stage is present as the raw counter
    // values will be correct.
    assign perf_instr_ret_wb_spec_o            = 1'b0;
    assign perf_instr_ret_compressed_wb_spec_o = 1'b0;
    assign perf_instr_ret_wb_o                 = instr_perf_count_id_i & en_wb_i &
                                                 ~(lsu_resp_valid_i & lsu_resp_err_i);
    assign perf_instr_ret_compressed_wb_o      = perf_instr_ret_wb_o & instr_is_compressed_id_i;

    // ready needs to be constant 1 without writeback stage (otherwise ID/EX stage will stall)
    assign ready_wb_o    = 1'b1;

    // Unused Writeback stage only IO & wiring
    // Assign inputs and internal wiring to unused signals to satisfy lint checks
    // Tie-off outputs to constant values
    logic           unused_clk;
    logic           unused_rst;
    wb_instr_type_e unused_instr_type_wb;
    logic [31:0]    unused_pc_id;
    logic           unused_dummy_instr_id;

    assign unused_clk            = clk_i;
    assign unused_rst            = rst_ni;
    assign unused_instr_type_wb  = instr_type_wb_i;
    assign unused_pc_id          = pc_id_i;
    assign unused_dummy_instr_id = dummy_instr_id_i;

    assign outstanding_load_wb_o  = 1'b0;
    assign outstanding_store_wb_o = 1'b0;
    assign pc_wb_o                = '0;
    assign rf_write_wb_o          = 1'b0;
    assign rf_wdata_fwd_wb_o      = 32'b0;
    assign instr_done_wb_o        = 1'b0;
  end

  assign rf_wdata_wb_mux[1] = rf_wdata_lsu_i;

  // RF write data can come from ID results (all RF writes that aren't because of loads will come
  // from here) or the LSU (RF writes for load data)
  assign rf_wdata_wb_o = ({32{rf_wdata_wb_mux_we[0]}} & rf_wdata_wb_mux[0]) |
                         ({32{rf_wdata_wb_mux_we[1]}} & rf_wdata_wb_mux[1]);
  assign rf_we_wb_o    = |rf_wdata_wb_mux_we;

  `DV_FCOV_SIGNAL_GEN_IF(logic, wb_valid, g_writeback_stage.wb_valid_q, WritebackStage)

  `ASSERT(RFWriteFromOneSourceOnly, $onehot0(rf_wdata_wb_mux_we))
endmodule
