// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

module prim_generic_pad_attr
  import prim_pad_wrapper_pkg::*;
#(
  parameter pad_type_e PadType = BidirStd // currently ignored in the generic model
) (
  output pad_attr_t attr_warl_o
);

  // Currently supported pad attributes of the generic pad library:
  //
  // - inversion
  // - virtual open drain
  // - keeper
  // - pullup / pulldown
  // - 1 driving strength bit
  //
  // Note that the last three attributes are not supported on Verilator.
  always_comb begin : p_attr
    attr_warl_o = '0;
    attr_warl_o.invert = 1'b1;
    attr_warl_o.virt_od_en = 1'b1;
    attr_warl_o.keep_en = 1'b1;
// Driving strength and pulls are not supported by Verilator
`ifndef VERILATOR
    attr_warl_o.pull_en = 1'b1;
    attr_warl_o.pull_select = 1'b1;
    // Only one driving strength bit is supported.
    attr_warl_o.drive_strength[0] = 1'b1;
`endif
  end

endmodule : prim_generic_pad_attr
