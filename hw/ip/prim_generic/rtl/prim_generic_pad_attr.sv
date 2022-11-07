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
  // Input-only:
  //
  // - inversion
  // - pullup / pulldown
  //
  // Bidirectional:
  //
  // - inversion
  // - virtual open drain
  // - pullup / pulldown
  // - 1 driving strength bit
  //
  // Note that the last three attributes are not supported on Verilator.
  if (PadType == InputStd) begin : gen_input_only_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
      attr_warl_o.pull_en = 1'b1;
      attr_warl_o.pull_select = 1'b1;
    end
  end else if (PadType == BidirStd ||
               PadType == BidirTol ||
               PadType == DualBidirTol ||
               PadType == BidirOd) begin : gen_bidir_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
      attr_warl_o.virt_od_en = 1'b1;
      attr_warl_o.pull_en = 1'b1;
      attr_warl_o.pull_select = 1'b1;
  // Driving strength is not supported by Verilator
  `ifndef VERILATOR
      // Only one driving strength bit is supported.
      attr_warl_o.drive_strength[0] = 1'b1;
  `endif
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

endmodule : prim_generic_pad_attr
