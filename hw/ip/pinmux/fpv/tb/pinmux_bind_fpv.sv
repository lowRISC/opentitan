// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module pinmux_bind_fpv;


  bind pinmux pinmux_assert_fpv i_pinmux_assert_fpv (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .periph_to_mio_i,
    .periph_to_mio_oe_i,
    .mio_to_periph_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i
  );


  bind pinmux tlul_assert #(
    .EndpointType("Device")
  ) i_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind pinmux pinmux_csr_assert_fpv i_pinmux_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg)
  );

endmodule : pinmux_bind_fpv
