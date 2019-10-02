// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This it the padctrl portion that has to be placed into the toplevel.
// It basically just wraps the regfile and outputs the configuration bits
// to be consumed on the chiplevel.
//

module padctrl (
  input                                       clk_i,
  input                                       rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                   tl_i,
  output tlul_pkg::tl_d2h_t                   tl_o,
  // pad attributes to chip level instance
  output logic[padctrl_reg_pkg::NMioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_o,
  output logic[padctrl_reg_pkg::NDioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_o
);

  //////////////////////////////////////////////////////
  // Regfile
  //////////////////////////////////////////////////////

  padctrl_reg_pkg::padctrl_reg2hw_t reg2hw;

  padctrl_reg_top i_reg_top (
    .clk_i  ,
    .rst_ni ,
    .tl_i   ,
    .tl_o   ,
    .reg2hw ,
    .devmode_i(1'b1)
  );

  //////////////////////////////////////////////////////
  // Connect attributes
  //////////////////////////////////////////////////////

  for (genvar k = 0; k < padctrl_reg_pkg::NMioPads; k++) begin : gen_mio_attr
    assign mio_attr_o[k] = reg2hw.mio_pads[k];
  end

  for (genvar k = 0; k < padctrl_reg_pkg::NDioPads; k++) begin : gen_dio_attr
    assign dio_attr_o[k] = reg2hw.dio_pads[k];
  end

endmodule : padctrl
