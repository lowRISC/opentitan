// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Shadowed register slice conforming to Comportibility guide.

module prim_subreg_shadow #(
  parameter int            DW       = 32  ,
  parameter                SWACCESS = "RW", // {RW, RO, WO, W1C, W1S, W0C, RC}
  parameter logic [DW-1:0] RESVAL   = '0    // reset value
) (
  input clk_i,
  input rst_ni,

  // From SW: valid for RW, WO, W1C, W1S, W0C, RC.
  // SW reads clear phase unless SWACCESS is RO.
  input          re,
  // In case of RC, top connects read pulse to we.
  input          we,
  input [DW-1:0] wd,

  // From HW: valid for HRW, HWO.
  input          de,
  input [DW-1:0] d,

  // Output to HW and Reg Read
  output logic          qe,
  output logic [DW-1:0] q,
  output logic [DW-1:0] qs,

  // Error conditions
  output logic err_update,
  output logic err_storage
);

  // Subreg control signals
  logic          phase_clear;
  logic          phase_q;
  logic          staged_we, shadow_we, committed_we;
  logic          staged_de, shadow_de, committed_de;

  // Subreg status and data signals
  logic          staged_qe, shadow_qe, committed_qe;
  logic [DW-1:0] staged_q,  shadow_q,  committed_q;
  logic [DW-1:0] committed_qs;

  // Effective write enable and write data signals.
  // These depend on we, de and wd, d, q as well as SWACCESS.
  logic          wr_en;
  logic [DW-1:0] wr_data;

  prim_subreg_arb #(
    .DW       ( DW       ),
    .SWACCESS ( SWACCESS )
  ) wr_en_data_arb (
    .we      ( we      ),
    .wd      ( wd      ),
    .de      ( de      ),
    .d       ( d       ),
    .q       ( q       ),
    .wr_en   ( wr_en   ),
    .wr_data ( wr_data )
  );

  // Phase clearing:
  // - SW reads clear phase unless SWACCESS is RO.
  // - In case of RO, SW should not interfere with update process.
  assign phase_clear = (SWACCESS == "RO") ? 1'b0 : re;

  // Phase tracker:
  // - Reads from SW clear the phase back to 0.
  // - Writes have priority (can come from SW or HW).
  always_ff @(posedge clk_i or negedge rst_ni) begin : phase_reg
    if (!rst_ni) begin
      phase_q <= 1'b0;
    end else if (wr_en) begin
      phase_q <= ~phase_q;
    end else if (phase_clear) begin
      phase_q <= 1'b0;
    end
  end

  // The staged register:
  // - Holds the 1's complement value.
  // - Written in Phase 0.
  assign staged_we = we & ~phase_q;
  assign staged_de = de & ~phase_q;
  prim_subreg #(
    .DW       ( DW       ),
    .SWACCESS ( SWACCESS ),
    .RESVAL   ( ~RESVAL  )
  ) staged_reg (
    .clk_i    ( clk_i     ),
    .rst_ni   ( rst_ni    ),
    .we       ( staged_we ),
    .wd       ( ~wd       ),
    .de       ( staged_de ),
    .d        ( ~d        ),
    .qe       ( staged_qe ),
    .q        ( staged_q  ),
    .qs       (           )
  );

  // The shadow register:
  // - Holds the 1's complement value.
  // - Written in Phase 1.
  // - Writes are ignored in case of update errors.
  // - Gets the value from the staged register.
  assign shadow_we = we & phase_q & ~err_update;
  assign shadow_de = de & phase_q & ~err_update;
  prim_subreg #(
    .DW       ( DW       ),
    .SWACCESS ( SWACCESS ),
    .RESVAL   ( ~RESVAL  )
  ) shadow_reg (
    .clk_i    ( clk_i     ),
    .rst_ni   ( rst_ni    ),
    .we       ( shadow_we ),
    .wd       ( staged_q  ),
    .de       ( shadow_de ),
    .d        ( staged_q  ),
    .qe       ( shadow_qe ),
    .q        ( shadow_q  ),
    .qs       (           )
  );

  // The committed register:
  // - Written in Phase 1.
  // - Writes are ignored in case of update errors.
  assign committed_we = shadow_we;
  assign committed_de = shadow_de;
  prim_subreg #(
    .DW       ( DW       ),
    .SWACCESS ( SWACCESS ),
    .RESVAL   ( RESVAL   )
  ) committed_reg (
    .clk_i    ( clk_i        ),
    .rst_ni   ( rst_ni       ),
    .we       ( committed_we ),
    .wd       ( wd           ),
    .de       ( committed_de ),
    .d        ( d            ),
    .qe       ( committed_qe ),
    .q        ( committed_q  ),
    .qs       ( committed_qs )
  );

  // Error detection - all bits must match.
  assign err_update  = (~staged_q != wr_data) ? phase_q & wr_en : 1'b0;
  assign err_storage = (~shadow_q != committed_q);

  // Remaining output assignments
  assign qe = staged_qe | shadow_qe | committed_qe;
  assign q  = committed_q;
  assign qs = committed_qs;

endmodule
