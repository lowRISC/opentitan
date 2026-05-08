// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Shadowed register slice conforming to Comportability guide.

`include "prim_assert.sv"

module prim_subreg_shadow
  import prim_subreg_pkg::*;
#(
  parameter int            DW       = 32,
  parameter sw_access_e    SwAccess = SwAccessRW,
  parameter logic [DW-1:0] RESVAL   = '0,    // reset value
  parameter bit            Mubi     = 1'b0
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

  // Subreg control signals
  logic          phase_clear;
  logic          phase_q;
  logic          shadow_we, committed_we;
  logic          committed_de;

  // Subreg status and data signals
  logic          committed_qe;
  logic [DW-1:0] shadow_wd, shadow_q, committed_q;
  logic [DW-1:0] committed_qs;

  // Effective write enable and write data signals.
  // These depend on we, de and wd, d, q as well as SwAccess.
  logic          wr_en;
  logic [DW-1:0] wr_data;

  // Arbite the incoming request versus the committed register.
  prim_subreg_arb #(
    .DW      (DW),
    .SwAccess(SwAccess),
    .Mubi    (Mubi)
  ) wr_en_data_arb (
    .we     (we),
    .wd     (wd),
    .de     (de),
    .d      (d),
    .q      (q),
    .wr_en  (wr_en),
    .wr_data(wr_data)
  );

  // Phase clearing:
  // - SW reads clear phase unless SwAccess is RO.
  // - In case of RO, SW should not interfere with update process.
  assign phase_clear = (SwAccess == SwAccessRO) ? 1'b0 : re;

  // Phase tracker:
  // - Reads from SW as well as update errors clear the phase back to 0.
  // - Writes have priority (can come from SW or HW).
  always_ff @(posedge clk_i or negedge rst_ni) begin : phase_reg
    if (!rst_ni) begin
      phase_q <= 1'b0;
    end else if (wr_en && !err_storage && !err_update) begin
      phase_q <= ~phase_q;
    end else if (phase_clear || err_storage || err_update) begin
      phase_q <= 1'b0;
    end
  end

  // The shadow register:
  // - Holds the 1's complement value.
  // - Unconditionally written in Phase 0.
  // - Restored to the committed value in case of update errors or if the phase gets cleared.
  // - Once storage error occurs, do not allow any further updates until reset.
  always_ff @(posedge clk_i or negedge rst_shadowed_ni) begin
    if (!rst_shadowed_ni) begin
      shadow_q <= ~RESVAL;
    end else if (shadow_we) begin
      shadow_q <= shadow_wd;
    end
  end

  if (InvertedSwAccess == SwAccess) begin : gen_shadow_reg_std
    // The standard case.
    logic          shadow_wr_en;
    logic [DW-1:0] shadow_wr_data;

    // Use the wr_data from the input arbiter above, invert it and re-arbite it versus the shadow
    // register. This is fine. The special W1S and W0C cases are handled separately.
    prim_subreg_arb #(
      .DW      (DW),
      .SwAccess(InvertedSwAccess),
      .Mubi    (Mubi)
    ) wr_en_data_arb_shadow (
      .we     (we),
      .wd     (~wr_data),
      .de     (de),
      .d      (~d),
      .q      (shadow_q),
      .wr_en  (shadow_wr_en),
      .wr_data(shadow_wr_data)
    );

    always_comb begin
      shadow_we = 1'b0;
      shadow_wd = shadow_wr_data;

      if (!err_storage) begin
        if (err_update || phase_clear) begin
          // Restore the committed value.
          shadow_we = 1'b1;
          shadow_wd = ~committed_q;
        end else if (!phase_q && shadow_wr_en) begin
          // Write the input value in Phase 0.
          shadow_we = 1'b1;
          shadow_wd = shadow_wr_data;
        end
      end
    end

    // Update errors can only occur in Phase 1.
    assign err_update = (~shadow_q != wr_data) ? phase_q & wr_en : 1'b0;

  end else begin : gen_shadow_reg_wxx
    // In case of W1S and W0C, the data value on the first write operation needs to be captured as
    // is - no matter whether the data value will actually have an effect. That way, we can still
    // capture inconsistent double writes which would otherwise be ignored due to the data value
    // filtering effect that W1S and W0C can have. This means we need separate prim_subreg_arb
    // arbiters for the two phases: The first is configured to RW, the second is set to
    // InvertedSwAccess.
    logic          shadow_wr_en_phase0, shadow_wr_en_phase1;
    logic [DW-1:0] shadow_wr_data_phase0, shadow_wr_data_phase1;

    // Use the input wd from software as is for the first phase to unconditionally capture it in
    // the shadow register.
    prim_subreg_arb #(
      .DW      (DW),
      .SwAccess(SwAccessRW),
      .Mubi    (Mubi)
    ) wr_en_data_arb_phase0 (
      .we     (we),
      .wd     (~wd),
      .de     (de),
      .d      (~d),
      .q      (shadow_q),
      .wr_en  (shadow_wr_en_phase0),
      .wr_data(shadow_wr_data_phase0)
    );

    // Use the wr_data from the input arbiter above, invert it and re-arbite it versus the inverted
    // committed register in the second phase. At this point, the shadow register contains the
    // unfiltered but negated input from software.
    prim_subreg_arb #(
      .DW      (DW),
      .SwAccess(InvertedSwAccess),
      .Mubi    (Mubi)
    ) wr_en_data_arb_phase1 (
      .we     (we),
      .wd     (~wr_data),
      .de     (de),
      .d      (~d),
      .q      (~committed_q),
      .wr_en  (shadow_wr_en_phase1),
      .wr_data(shadow_wr_data_phase1)
    );

    always_comb begin
      shadow_we = 1'b0;
      shadow_wd = shadow_wr_data_phase0;

      if (!err_storage) begin
        if (err_update || phase_clear) begin
          // Restore the committed value.
          shadow_we = 1'b1;
          shadow_wd = ~committed_q;
        end else if (!phase_q) begin
          // Capture the input value in Phase 0.
          shadow_we = shadow_wr_en_phase0;
          shadow_wd = shadow_wr_data_phase0;
        end else begin
          // Write the corrected value in Phase 1.
          shadow_we = shadow_wr_en_phase1;
          shadow_wd = shadow_wr_data_phase1;
        end
      end
    end

    // Update errors can only occur in Phase 1. At this point, the shadow register contains the
    // unfiltered but negated input from software, i.e., the check has to be performed based on the
    // unfiltered input. Note: the unfiltered input wd may be X - we should only use it if wr_en is
    // asserted.
    assign err_update = (phase_q && wr_en) ? (~shadow_q != wd) : 1'b0;
  end

  // The committed register:
  // - Written in Phase 1.
  // - Writes are ignored in case of update and storage errors.
  assign committed_we = we & phase_q & ~err_update & ~err_storage;
  assign committed_de = de & phase_q & ~err_update & ~err_storage;
  prim_subreg #(
    .DW      (DW),
    .SwAccess(SwAccess),
    .RESVAL  (RESVAL),
    .Mubi    (Mubi)
  ) committed_reg (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .we    (committed_we),
    .wd    (wr_data),
    .de    (committed_de),
    .d     (d),
    .qe    (committed_qe),
    .q     (committed_q),
    .ds    (ds),
    .qs    (committed_qs)
  );

  // Output phase for hwext.
  assign phase = phase_q;

  // Storage errors are only signaled in Phase 0. In Phase 1, the two registers are expected to be
  // out of sync.
  assign err_storage = (~shadow_q != committed_q) ? ~phase_q : 1'b0;

  // Remaining output assignments
  assign qe = committed_qe;
  assign q  = committed_q;
  assign qs = committed_qs;

endmodule
