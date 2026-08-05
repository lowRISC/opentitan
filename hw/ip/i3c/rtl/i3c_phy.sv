// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C PHY model.

module i3c_phy #(
  parameter int unsigned NumSDALanes = 1
) (
  // Pull-up enables.
  //
  // Note: The pull-up resistances need to be quite small so it may be more appropriate to drive
  // the enables off-chip such that the PHY is not concerned with pull-ups.
  input                   scl_pu_en_i,
  input                   sda_pu_en_i,

  // SCL driver enable.
  input                   scl_pp_en_i,
  // SCL signal from IP block.
  input                   scl_i,

  // SDA driver enables.
  input                   sda_pp_en_i,
  input                   sda_od_en_i,
  // SDA signal from IP block.
  input [NumSDALanes-1:0] sda_i,

  // I3C I/O signals.
  inout                   scl_io,
  inout [NumSDALanes-1:0] sda_io
);

  `ifdef VERILATOR
  // Serial CLock output.
  assign scl_io = scl_pp_en_i ? scl_i : (scl_pu_en_i ? 1'b1 : 1'bZ);
  // Serial DA output.
  for (genvar d = 0; d < NumSDALanes; d++) begin : gen_sda_vlt
    assign sda_io[d] = sda_pp_en_i ? sda_i[d] :
        ((sda_od_en_i & !sda_i[d]) ? 1'b0 :
                      (sda_pu_en_i ? 1'b1 : 1'bZ));
  end
  `else
  // Push-pull drivers.
  assign (strong0, strong1) scl_io = scl_pp_en_i ? scl_i : 1'bZ;
  assign (strong0, strong1) sda_io = sda_pp_en_i ? sda_i :   'Z;
  // Open drain drivers.
  for (genvar d = 0; d < NumSDALanes; d++) begin : gen_sda
    assign (strong0, weak1) sda_io[d] = (sda_od_en_i & !sda_i[d]) ? 1'b0 : 1'bZ;
  end
  // Pull-ups for open drain operation.
  assign (weak0, pull1) scl_io = scl_pu_en_i ? 1'b1 : 1'bZ;
  assign (weak0, pull1) sda_io = sda_pu_en_i ?   '1 :   'Z;
  `endif

endmodule
