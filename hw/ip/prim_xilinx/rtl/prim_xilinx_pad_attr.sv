// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

module prim_xilinx_pad_attr
  import prim_pad_wrapper_pkg::*;
#(
  // This parameter is ignored in this Xilinx variant.
  parameter pad_type_e PadType = BidirStd
) (
  output pad_attr_t attr_warl_o
);

  // Currently supporte pad attributes of the Xilinx pad library.
  //
  // - inversion
  // - virtual open drain
  //
  // TODO: add support for dynamic pull-up/down using the PULLUP/PULLDOWN primitives
  // from the vivado-7series library (https://www.xilinx.com/support/documentation/
  // sw_manuals/xilinx2020_2/ug953-vivado-7series-libraries.pdf)
  always_comb begin : p_attr
    attr_warl_o = '0;
    attr_warl_o.invert = 1'b1;
    attr_warl_o.virt_od_en = 1'b1;
  end

endmodule : prim_xilinx_pad_attr
