// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// IHP130 (sg13cmos5l_io) pad attribute WARL mask. Must match prim_pad_wrapper: the IO cells have
// no pulls and a fixed 4 mA drive, so only inversion, virtual open drain and input disable are
// supported. Analog pads are not supported.

`include "prim_assert.sv"

module prim_pad_attr
  import prim_pad_wrapper_pkg::*;
#(
  parameter pad_type_e PadType = BidirStd
) (
  output pad_attr_t attr_warl_o
);

  if (PadType == InputStd) begin : gen_input_only_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
      attr_warl_o.input_disable = 1'b1;
    end
  end else if (PadType == BidirStd ||
               PadType == BidirTol ||
               PadType == DualBidirTol ||
               PadType == BidirOd) begin : gen_bidir_warl
    always_comb begin : p_attr
      attr_warl_o = '0;
      attr_warl_o.invert = 1'b1;
      attr_warl_o.virt_od_en = 1'b1;
      attr_warl_o.input_disable = 1'b1;
    end
  end else begin : gen_invalid_config
    // this should throw link warnings in elaboration
    assert_static_in_generate_config_not_available
        assert_static_in_generate_config_not_available();
  end

endmodule : prim_pad_attr
