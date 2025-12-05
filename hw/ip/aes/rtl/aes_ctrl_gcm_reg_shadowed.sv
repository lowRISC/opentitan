// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES Galois/Counter Mode (GCM) shadowed control register
//
// This module implements the shadowed AES GCM control register. The main differences compared
// to implementing the register as part of the auto-generated aes_reg_top.sv are:
//
// 1. The hardware can block updates to the GCM control register from software.
//    Whenever the module is busy, GCM control register writes are ignored.
// 2. Invalid values written by software are resolved to valid configurations.

`include "prim_assert.sv"

module aes_ctrl_gcm_reg_shadowed
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit AESGCMEnable = 1
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic rst_shadowed_ni,
  // Main control
  output logic       qe_o, // software wants to write
  input  logic       we_i, // hardware grants software write
  output gcm_phase_e gcm_phase_o,
  output logic [4:0] num_valid_bytes_o,

  // Alerts
  output logic err_update_o,
  output logic err_storage_o,

  // Bus interface
  input  aes_reg2hw_ctrl_gcm_shadowed_reg_t reg2hw_ctrl_gcm_i,
  output aes_hw2reg_ctrl_gcm_shadowed_reg_t hw2reg_ctrl_gcm_o
);

  // Signals
  logic          err_update_gcm_phase;
  logic          err_update_num_valid_bytes;
  logic          err_storage_gcm_phase;
  logic          err_storage_num_valid_bytes;

  // Get and forward write enable. Writes are only allowed if the module is idle.
  assign qe_o = reg2hw_ctrl_gcm_i.phase.qe & reg2hw_ctrl_gcm_i.num_valid_bytes.qe;

  if (AESGCMEnable) begin : gen_ctrl_gcm_reg_shadowed
    ctrl_gcm_reg_t ctrl_gcm_wd;
    gcm_phase_e    gcm_phase_reg_if, gcm_phase;
    logic [4:0]    num_valid_bytes;

    // Get and resolve values from register interface.
    assign gcm_phase_reg_if = gcm_phase_e'(reg2hw_ctrl_gcm_i.phase.q);
    always_comb begin : gcm_phase_get
      // Resolve unsupported input values.
      unique case (gcm_phase_reg_if)
        GCM_INIT:    gcm_phase = GCM_INIT;
        GCM_RESTORE: gcm_phase = GCM_RESTORE;
        GCM_AAD:     gcm_phase = GCM_AAD;
        GCM_TEXT:    gcm_phase = GCM_TEXT;
        GCM_SAVE:    gcm_phase = GCM_SAVE;
        GCM_TAG:     gcm_phase = GCM_TAG;
        default:     gcm_phase = GCM_INIT; // Unsupported values are mapped to GCM_INIT.
      endcase

      // Only a subset of next phase transitions are allowed.
      unique case (gcm_phase_o)
        GCM_INIT: begin
          gcm_phase = gcm_phase == GCM_RESTORE ||
                      gcm_phase == GCM_AAD     ||
                      gcm_phase == GCM_TEXT    ||
                      gcm_phase == GCM_TAG     ? gcm_phase : gcm_phase_o;
        end

        GCM_RESTORE: begin
          gcm_phase = gcm_phase == GCM_INIT ||
                      gcm_phase == GCM_AAD  ||
                      gcm_phase == GCM_TEXT ? gcm_phase : gcm_phase_o;
        end

        GCM_AAD: begin
          gcm_phase = gcm_phase == GCM_INIT ||
                      gcm_phase == GCM_TEXT ||
                      gcm_phase == GCM_SAVE ||
                      gcm_phase == GCM_TAG  ? gcm_phase : gcm_phase_o;
        end

        GCM_TEXT: begin
          gcm_phase = gcm_phase == GCM_INIT ||
                      gcm_phase == GCM_SAVE ||
                      gcm_phase == GCM_TAG  ? gcm_phase : gcm_phase_o;
        end

        GCM_SAVE: begin
          gcm_phase = gcm_phase == GCM_INIT ? gcm_phase : gcm_phase_o;
        end

        GCM_TAG: begin
          gcm_phase = gcm_phase == GCM_INIT ? gcm_phase : gcm_phase_o;
        end

        default: begin
          gcm_phase = gcm_phase_o; // If we end up in an unspported value (which should never
                                   // happen), keep it.
        end
      endcase
    end
    assign ctrl_gcm_wd.phase = gcm_phase;

    assign num_valid_bytes = reg2hw_ctrl_gcm_i.num_valid_bytes.q;
    // Unsupported values are mapped to 16.
    assign ctrl_gcm_wd.num_valid_bytes =
        ((num_valid_bytes == 5'd0) || (num_valid_bytes > 5'd16)) ? 5'd16 : num_valid_bytes;

    // SEC_CM: GCM.CONFIG.SHADOW
    // Instantiate one shadowed register primitive per field. An update error in a field should
    // only prevent the update of the affected field.
    prim_subreg_shadow #(
      .DW      ($bits(gcm_phase_e)),
      .SwAccess(prim_subreg_pkg::SwAccessWO),
      .RESVAL  (AES_CTRL_GCM_SHADOWED_PHASE_RESVAL)
    ) u_ctrl_gcm_reg_shadowed_phase (
      .clk_i,
      .rst_ni,
      .rst_shadowed_ni,
      .re         (reg2hw_ctrl_gcm_i.phase.re),
      .we         (we_i),
      .wd         ({ctrl_gcm_wd.phase}),
      .de         (1'b0),
      .d          ('0),
      .qe         (),
      .q          (hw2reg_ctrl_gcm_o.phase.d),
      .qs         (),
      .ds         (),
      .phase      (),
      .err_update (err_update_gcm_phase),
      .err_storage(err_storage_gcm_phase)
    );

    prim_subreg_shadow #(
      .DW      (5),
      .SwAccess(prim_subreg_pkg::SwAccessWO),
      .RESVAL  (AES_CTRL_GCM_SHADOWED_NUM_VALID_BYTES_RESVAL)
    ) u_ctrl_gcm_reg_shadowed_num_valid_bytes (
      .clk_i,
      .rst_ni,
      .rst_shadowed_ni,
      .re         (reg2hw_ctrl_gcm_i.num_valid_bytes.re),
      .we         (we_i),
      .wd         ({ctrl_gcm_wd.num_valid_bytes}),
      .de         (1'b0),
      .d          ('0),
      .qe         (),
      .q          (hw2reg_ctrl_gcm_o.num_valid_bytes.d),
      .qs         (),
      .ds         (),
      .phase      (),
      .err_update (err_update_num_valid_bytes),
      .err_storage(err_storage_num_valid_bytes)
    );
  end else begin : gen_no_ctrl_gcm_reg_shadowed
    // Tie off unused inputs.
    logic unused_ctrl_gcm;
    assign unused_ctrl_gcm = ^{reg2hw_ctrl_gcm_i.phase.re,
                               reg2hw_ctrl_gcm_i.phase.q,
                               reg2hw_ctrl_gcm_i.num_valid_bytes.re,
                               reg2hw_ctrl_gcm_i.num_valid_bytes.q};
    logic unused_we;
    assign unused_we = we_i;

    logic unused_clk;
    logic unused_rst;
    logic unused_rst_shadowed;
    assign unused_clk = clk_i;
    assign unused_rst = rst_ni;
    assign unused_rst_shadowed = rst_shadowed_ni;

    // Tie off control signals.
    assign hw2reg_ctrl_gcm_o.phase.d           = {GCM_INIT};
    assign hw2reg_ctrl_gcm_o.num_valid_bytes.d = 5'd16;

    // Tie off error signals.
    assign err_update_gcm_phase        = 1'b0;
    assign err_update_num_valid_bytes  = 1'b0;
    assign err_storage_gcm_phase       = 1'b0;
    assign err_storage_num_valid_bytes = 1'b0;
  end

  // Collect alerts.
  assign err_update_o = err_update_gcm_phase | err_update_num_valid_bytes;
  assign err_storage_o = err_storage_gcm_phase | err_storage_num_valid_bytes;

  // Generate shorter references.
  // Doing that here as opposed to in aes_core avoids several Verilator lint errors.
  assign gcm_phase_o       = gcm_phase_e'(hw2reg_ctrl_gcm_o.phase.d);
  assign num_valid_bytes_o = hw2reg_ctrl_gcm_o.num_valid_bytes.d;

endmodule
