// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module padctrl_bind;

  bind padring padring_assert padring_assert (
    .*
  );

  bind padctrl padctrl_assert #(
    .Impl(Impl)
  ) padctrl_assert (
    .*
  );

  bind padctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

endmodule : padctrl_bind
