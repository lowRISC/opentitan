// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Shadowed register slice conforming to Comportibility guide.

`include "prim_assert.sv"

module prim_subreg_shadow
  import prim_subreg_pkg::*;
#(
  parameter int            DW       = 32,
  parameter sw_access_e    SwAccess = SwAccessRW,
  parameter logic [DW-1:0] RESVAL   = '0    // reset value
) (
  input clk_i,
  input rst_ni,
  input rst_shadowed_ni,

  // From SW: valid for RW, WO, W1C, W1S, W0C, RC.
  // SW reads clear phase unless SwAccess is RO.
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
  output logic [DW-1:0] ds,
  output logic [DW-1:0] qs,

  // Phase output to HW
  output logic phase,

  // Error conditions
  output logic err_update,
  output logic err_storage
);

  // Since the shadow register works with the 1's complement value,
  // we need to invert the polarity of the SW access if it is either "W1S" or "W0C".
  // W1C is forbidden since the W0S complement is not implemented.
  `ASSERT_INIT(CheckSwAccessIsLegal_A,
      SwAccess inside {SwAccessRW, SwAccessRO, SwAccessWO, SwAccessW1S, SwAccessW0C})
  localparam sw_access_e InvertedSwAccess = (SwAccess == SwAccessW1S) ? SwAccessW0C :
                                            (SwAccess == SwAccessW0C) ? SwAccessW1S : SwAccess;

  // For the staging register, we set the SwAccess to RW in case of W1S and W0C in
  // order to always capture the data value on the first write operation - no matter
  // whether the data value will actually have an effect. That way, we can still capture
  // inconsistent double writes which would otherwise be ignored due to the data value filtering
  // effect that W1S and W0C can have.
  localparam sw_access_e StagedSwAccess = (SwAccess == SwAccessW1S) ? SwAccessRW :
                                          (SwAccess == SwAccessW0C) ? SwAccessRW : SwAccess;

  // Subreg control signals
  logic          phase_clear;
  logic          phase_q;
  logic          staged_we, shadow_we, committed_we;
  logic          staged_de, shadow_de, committed_de;

  // Subreg status and data signals
  logic          committed_qe;
  logic [DW-1:0] staged_q,  shadow_q,  committed_q;
  logic [DW-1:0] committed_qs;

  // Effective write enable and write data signals.
  // These depend on we, de and wd, d, q as well as SwAccess.
  logic          wr_en;
  logic [DW-1:0] wr_data;

  prim_subreg_arb #(
    .DW       ( DW       ),
    .SwAccess ( SwAccess )
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
  // - SW reads clear phase unless SwAccess is RO.
  // - In case of RO, SW should not interfere with update process.
  assign phase_clear = (SwAccess == SwAccessRO) ? 1'b0 : re;

  // Phase tracker:
  // - Reads from SW clear the phase back to 0.
  // - Writes have priority (can come from SW or HW).
  always_ff @(posedge clk_i or negedge rst_ni) begin : phase_reg
    if (!rst_ni) begin
      phase_q <= 1'b0;
    end else if (wr_en && !err_storage) begin
      phase_q <= ~phase_q;
    end else if (phase_clear || err_storage) begin
      phase_q <= 1'b0;
    end
  end

  // The staged register:
  // - Holds the 1's complement value.
  // - Written in Phase 0.
  // - Once storage error occurs, do not allow any further update until reset
  assign staged_we = we & ~phase_q & ~err_storage;
  assign staged_de = de & ~phase_q & ~err_storage;
  prim_subreg #(
    .DW       ( DW             ),
    .SwAccess ( StagedSwAccess ),
    .RESVAL   ( ~RESVAL        )
  ) staged_reg (
    .clk_i    ( clk_i     ),
    .rst_ni   ( rst_ni    ),
    .we       ( staged_we ),
    .wd       ( ~wr_data  ),
    .de       ( staged_de ),
    .d        ( ~d        ),
    .qe       (           ),
    .q        ( staged_q  ),
    .ds       (           ),
    .qs       (           )
  );

  // The shadow register:
  // - Holds the 1's complement value.
  // - Written in Phase 1.
  // - Writes are ignored in case of update errors.
  // - Gets the value from the staged register.
  // - Once storage error occurs, do not allow any further update until reset
  assign shadow_we = we & phase_q & ~err_update & ~err_storage;
  assign shadow_de = de & phase_q & ~err_update & ~err_storage;
  prim_subreg #(
    .DW       ( DW               ),
    .SwAccess ( InvertedSwAccess ),
    .RESVAL   ( ~RESVAL          )
  ) shadow_reg (
    .clk_i    ( clk_i           ),
    .rst_ni   ( rst_shadowed_ni ),
    .we       ( shadow_we       ),
    .wd       ( staged_q        ),
    .de       ( shadow_de       ),
    .d        ( staged_q        ),
    .qe       (                 ),
    .q        ( shadow_q        ),
    .ds       (                 ),
    .qs       (                 )
  );

  // The committed register:
  // - Written in Phase 1.
  // - Writes are ignored in case of update errors.
  assign committed_we = shadow_we;
  assign committed_de = shadow_de;
  prim_subreg #(
    .DW       ( DW       ),
    .SwAccess ( SwAccess ),
    .RESVAL   ( RESVAL   )
  ) committed_reg (
    .clk_i    ( clk_i        ),
    .rst_ni   ( rst_ni       ),
    .we       ( committed_we ),
    .wd       ( wr_data      ),
    .de       ( committed_de ),
    .d        ( d            ),
    .qe       ( committed_qe ),
    .q        ( committed_q  ),
    .ds       ( ds           ),
    .qs       ( committed_qs )
  );

  // Output phase for hwext.
  assign phase = phase_q;

  // Error detection - all bits must match.
  assign err_update  = (~staged_q != wr_data) ? phase_q & wr_en : 1'b0;
  assign err_storage = (~shadow_q != committed_q);

  // Remaining output assignments
  assign qe = committed_qe;
  assign q  = committed_q;
  assign qs = committed_qs;

endmodule
