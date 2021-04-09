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

  // Currently supported pad attributes of the Xilinx pad library.
  //
  // Input-only:
  //
  // - inversion
  //
  // Bidirectional:
  //
  // - inversion
  // - virtual open drain
  //
  if (PadType == InputStd) begin : gen_input_only_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
    end
  end else if (PadType == BidirStd ||
               PadType == BidirTol ||
               PadType == BidirOd) begin : gen_bidir_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
      attr_warl_o.virt_od_en = 1'b1;
    end
  end else if (PadType == AnalogIn0) begin : gen_analog0_warl
    // The analog pad type is basically just a feedthrough,
    // and does hence not support any of the attributes.
    always_comb begin : p_attr
      attr_warl_o = '0;
    end
  end else begin : gen_invalid_config
    // this should throw link warnings in elaboration
    assert_static_in_generate_config_not_available
        assert_static_in_generate_config_not_available();
  end


endmodule : prim_xilinx_pad_attr
