// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: ast_dft
// *Module Description: AST DFT
//############################################################################

`include "prim_assert.sv"

module ast_dft (
  output ast_pkg::ast_obs_ctrl_t obs_ctrl_o,  // Observe Control
  output logic [ast_pkg::Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT observed outputs
  // memories read-write margins
  output ast_pkg::dpm_rm_t dpram_rmf_o,     // Dual Port RAM Read-write Margin Fast
  output ast_pkg::dpm_rm_t dpram_rml_o,     // Dual Port RAM Read-write Margin sLow
  output ast_pkg::spm_rm_t spram_rm_o,      // Single Port RAM Read-write Margin
  output ast_pkg::spm_rm_t sprgf_rm_o,      // Single Port Reg-File Read-write Margin
  output ast_pkg::spm_rm_t sprom_rm_o       // Single Port ROM Read-write Margin
);

// DFT to AST Digital PADs
assign ast2padmux_o  = {ast_pkg::Ast2PadOutWidth{1'b0}};

assign obs_ctrl_o = '{
                       obgsl: 4'h0,
                       obmsl: ast_pkg::ObsNon,
                       obmen: prim_mubi_pkg::MuBi4False
                     };


////////////////////////////////////////
// Memories Read-write Margins
////////////////////////////////////////
assign dpram_rmf_o = 10'h000;
assign dpram_rml_o = 10'h000;
assign spram_rm_o  = 5'h00;
assign sprgf_rm_o  = 5'h00;
assign sprom_rm_o  = 5'h00;

endmodule : ast_dft
